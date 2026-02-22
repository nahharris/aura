//! AST-to-bytecode compiler for the Aura language.
//!
//! The compiler performs a single-pass walk of the [`Program`] AST and emits
//! bytecode into a [`Chunk`].  It does **not** perform type checking; that is
//! deferred to a future static analysis pass.
//!
//! # Scope model
//!
//! Locals are tracked in a flat `Vec<Local>` that mirrors the VM's value stack.
//! Each `ScopeDepth` marks an entry point; when a scope ends, all locals at
//! that depth are popped.
//!
//! Upvalues are resolved by walking enclosing `CompilerFrame`s; a chain of
//! `UpvalueDesc`s is built for each closure.
//!
//! # Module-level code
//!
//! The top-level [`Program`] is compiled into a synthetic `defn __module__`
//! whose chunk is the "module chunk".  Global definitions are emitted as
//! `DefineGlobal` instructions.

use std::fmt;

use crate::ast::*;
use crate::bytecode::{Chunk, Constant, FnProto, OpCode, UpvalueDesc};
use crate::token::{Span, StringPart};

// ─────────────────────────────────────────────────────────────────────────────
// Error type
// ─────────────────────────────────────────────────────────────────────────────

/// A compile-time error.
#[derive(Debug, Clone)]
pub struct CompileError {
    pub message: String,
    pub span: Span,
}

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}:{}] {}", self.span.line, self.span.col, self.message)
    }
}

impl std::error::Error for CompileError {}

// ─────────────────────────────────────────────────────────────────────────────
// Local variable tracker
// ─────────────────────────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
struct Local {
    name: String,
    depth: u32,
    /// `true` once `CloseUpvalue` has been emitted for this slot.
    is_captured: bool,
}

// ─────────────────────────────────────────────────────────────────────────────
// Compiler frame (one per function / closure being compiled)
// ─────────────────────────────────────────────────────────────────────────────

#[allow(dead_code)]
struct Frame {
    /// Bytecode being built for this function.
    chunk: Chunk,
    /// The function's name (for diagnostics and FnProto).
    name: String,
    /// Locals in the current function.
    locals: Vec<Local>,
    /// Current scope depth (0 = module level inside a function).
    scope_depth: u32,
    /// Upvalue descriptors accumulated while compiling this function.
    upvalues: Vec<UpvalueDesc>,
    /// Arity (number of parameters).
    arity: u8,
}

impl Frame {
    fn new(name: impl Into<String>, arity: u8) -> Self {
        Frame {
            chunk: Chunk::new(),
            name: name.into(),
            locals: Vec::new(),
            scope_depth: 0,
            upvalues: Vec::new(),
            arity,
        }
    }

    fn current_line(&self) -> u32 {
        // Use the last emitted line, or 0.
        self.chunk.lines.last().copied().unwrap_or(0)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Loop context (for break / continue patching)
// ─────────────────────────────────────────────────────────────────────────────

struct LoopCtx {
    /// Label atom (if any).
    label: Option<String>,
    /// Byte offset of the loop's start (for `continue` back-jumps).
    loop_start: usize,
    /// Patch offsets for `break` forward jumps.
    break_patches: Vec<usize>,
}

// ─────────────────────────────────────────────────────────────────────────────
// Compiler
// ─────────────────────────────────────────────────────────────────────────────

/// The Aura bytecode compiler.
///
/// Create one with [`Compiler::new`], then call [`Compiler::compile_program`].
pub struct Compiler {
    /// Stack of active function frames (innermost last).
    frames: Vec<Frame>,
    /// Active loop contexts (innermost last), for break/continue resolution.
    loops: Vec<LoopCtx>,
    /// Accumulated errors (non-fatal; compilation continues).
    errors: Vec<CompileError>,
}

impl Default for Compiler {
    fn default() -> Self {
        Self::new()
    }
}

impl Compiler {
    /// Create a new compiler for a top-level module.
    pub fn new() -> Self {
        let module_frame = Frame::new("__module__", 0);
        Compiler {
            frames: vec![module_frame],
            loops: Vec::new(),
            errors: Vec::new(),
        }
    }

    // ── Error helpers ────────────────────────────────────────────────────────

    fn error(&mut self, msg: impl Into<String>, span: Span) {
        self.errors.push(CompileError {
            message: msg.into(),
            span,
        });
    }

    // ── Frame helpers ────────────────────────────────────────────────────────

    fn frame(&self) -> &Frame {
        self.frames.last().unwrap()
    }

    fn frame_mut(&mut self) -> &mut Frame {
        self.frames.last_mut().unwrap()
    }

    fn chunk_mut(&mut self) -> &mut Chunk {
        &mut self.frames.last_mut().unwrap().chunk
    }

    // ── Emit helpers ─────────────────────────────────────────────────────────

    fn emit(&mut self, op: OpCode, line: u32) {
        self.chunk_mut().emit_op(op, line);
    }

    fn emit_u8(&mut self, op: OpCode, operand: u8, line: u32) {
        self.chunk_mut().emit_op_u8(op, operand, line);
    }

    fn emit_u16(&mut self, op: OpCode, operand: u16, line: u32) {
        self.chunk_mut().emit_op_u16(op, operand, line);
    }

    fn emit_op_u16_u8(&mut self, op: OpCode, operand_u16: u16, operand_u8: u8, line: u32) {
        self.chunk_mut()
            .emit_op_u16_u8(op, operand_u16, operand_u8, line);
    }

    fn emit_jump(&mut self, op: OpCode, line: u32) -> usize {
        self.chunk_mut().emit_jump(op, line)
    }

    fn patch_jump(&mut self, offset: usize) {
        self.chunk_mut().patch_jump(offset);
    }

    fn emit_const(&mut self, c: Constant, line: u32) {
        let idx = self.chunk_mut().add_constant(c);
        self.emit_u16(OpCode::Const, idx, line);
    }

    // ── Scope management ─────────────────────────────────────────────────────

    fn begin_scope(&mut self) {
        self.frame_mut().scope_depth += 1;
    }

    fn end_scope(&mut self, line: u32) {
        let depth = self.frame().scope_depth;
        self.frame_mut().scope_depth -= 1;

        // Pop all locals at the closing depth.
        while let Some(local) = self.frame().locals.last() {
            if local.depth < depth {
                break;
            }
            let captured = local.is_captured;
            let slot = (self.frame().locals.len() - 1) as u8;
            self.frame_mut().locals.pop();
            if captured {
                self.emit_u8(OpCode::CloseUpvalue, slot, line);
            } else {
                self.emit(OpCode::Pop, line);
            }
        }
    }

    // ── Local variable resolution ─────────────────────────────────────────────

    fn declare_local(&mut self, name: impl Into<String>, depth: u32) -> u8 {
        let idx = self.frame().locals.len() as u8;
        self.frame_mut().locals.push(Local {
            name: name.into(),
            depth,
            is_captured: false,
        });
        idx
    }

    fn resolve_local(&self, name: &str) -> Option<u8> {
        let locals = &self.frame().locals;
        for (i, local) in locals.iter().enumerate().rev() {
            if local.name == name {
                return Some(i as u8);
            }
        }
        None
    }

    fn resolve_upvalue(&mut self, name: &str, frame_idx: usize) -> Option<u8> {
        if frame_idx == 0 {
            return None; // reached the module frame; treat as global
        }

        // Try to find a local in the immediately enclosing frame.
        let local_idx = {
            let enclosing = &self.frames[frame_idx - 1].locals;
            enclosing
                .iter()
                .enumerate()
                .rev()
                .find(|(_, l)| l.name == name)
                .map(|(i, _)| i as u8)
        };

        if let Some(idx) = local_idx {
            // Mark the local as captured.
            self.frames[frame_idx - 1].locals[idx as usize].is_captured = true;
            return Some(self.add_upvalue(
                frame_idx,
                UpvalueDesc {
                    is_local: true,
                    index: idx,
                },
            ));
        }

        // Recurse into outer frames.
        if let Some(upvalue_idx) = self.resolve_upvalue(name, frame_idx - 1) {
            return Some(self.add_upvalue(
                frame_idx,
                UpvalueDesc {
                    is_local: false,
                    index: upvalue_idx,
                },
            ));
        }

        None
    }

    fn add_upvalue(&mut self, frame_idx: usize, desc: UpvalueDesc) -> u8 {
        let uvs = &mut self.frames[frame_idx].upvalues;
        // Deduplicate.
        if let Some(i) = uvs
            .iter()
            .position(|u| u.is_local == desc.is_local && u.index == desc.index)
        {
            return i as u8;
        }
        let idx = uvs.len() as u8;
        uvs.push(desc);
        idx
    }

    // ── Name resolution ───────────────────────────────────────────────────────

    fn resolve_name(&mut self, name: &str, span: Span) {
        let frame_idx = self.frames.len() - 1;

        if let Some(local_idx) = self.resolve_local(name) {
            self.emit_u8(OpCode::LoadLocal, local_idx, span.line);
            return;
        }

        if let Some(uv_idx) = self.resolve_upvalue(name, frame_idx) {
            self.emit_u8(OpCode::LoadUpvalue, uv_idx, span.line);
            return;
        }

        // Fall back to global.
        let name_idx = self.chunk_mut().add_str(name);
        self.emit_u16(OpCode::LoadGlobal, name_idx, span.line);
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Top-level compilation
    // ─────────────────────────────────────────────────────────────────────────

    /// Compile a full [`Program`] and return the module-level [`Chunk`].
    pub fn compile_program(mut self, program: Program) -> Result<Chunk, Vec<CompileError>> {
        // Detect whether the program defines a top-level `defn main`.
        let has_main = program.items.iter().any(|item| {
            matches!(
                item,
                Item::Decl(Decl {
                    kind: DeclKind::Defn(DefnDecl { name, receiver: None, .. }),
                    ..
                }) if name == "main"
            )
        });

        for item in program.items {
            match item {
                Item::Use(_use_decl) => {
                    // Module loading is handled by the VM at runtime.
                    // The compiler just emits a LoadGlobal + DefineGlobal sequence.
                    // For now, use declarations are no-ops at compile time.
                }
                Item::Decl(decl) => self.compile_decl(decl),
            }
        }

        let line = self.frame().current_line();

        if has_main {
            // Call the top-level `main` function as the program entry point.
            let name_idx = self.chunk_mut().add_str("main");
            self.emit_u16(OpCode::LoadGlobal, name_idx, line);
            self.emit_u8(OpCode::Call, 0, line);
            self.emit(OpCode::Pop, line);
        } else {
            self.errors.push(CompileError {
                message: "program has no `defn main()` entry point".into(),
                span: Span {
                    start: 0,
                    end: 0,
                    line: 1,
                    col: 1,
                },
            });
        }

        // Implicit `return null` at the end of the module chunk.
        self.emit(OpCode::Null, line);
        self.emit(OpCode::Return, line);

        if self.errors.is_empty() {
            Ok(self.frames.pop().unwrap().chunk)
        } else {
            Err(self.errors)
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Declarations
    // ─────────────────────────────────────────────────────────────────────────

    fn compile_decl(&mut self, decl: Decl) {
        match decl.kind {
            DeclKind::Def(d) => self.compile_def(d),
            DeclKind::Defn(d) => self.compile_defn(d),
            DeclKind::Deftype(d) => self.compile_deftype(d),
            DeclKind::Defmacro(_) => {
                // defmacro is parsed but not yet compiled; ignore silently.
            }
        }
    }

    fn compile_def(&mut self, def: DefDecl) {
        for (name, init) in def.bindings {
            let span = init.span();
            self.compile_expr(init);
            let name_idx = self.chunk_mut().add_str(&name);
            self.emit_u16(OpCode::DefineGlobal, name_idx, span.line);
        }
    }

    fn compile_defn(&mut self, defn: DefnDecl) {
        let span = defn.span;
        let full_name = match &defn.receiver {
            Some(recv) => format!("{}.{}", recv, defn.name),
            None => defn.name.clone(),
        };

        // Build the function proto by compiling the body in a new frame.
        let proto = self.compile_fn(full_name.clone(), &defn.params, defn.body, span);

        // Emit Closure instruction (captures no upvalues at module level normally).
        self.emit_const(Constant::FnProto(Box::new(proto)), span.line);
        // Wrap in a closure object (even if no upvalues).
        let uv_count = 0u16; // module-level defns have no upvalues to capture.
        let _ = uv_count; // used by VM at runtime
                          // Emit DefineGlobal.
        let name_idx = self.chunk_mut().add_str(&full_name);
        self.emit_u16(OpCode::DefineGlobal, name_idx, span.line);
    }

    fn compile_deftype(&mut self, dt: DeftypeDecl) {
        // `deftype Point(x: Int, y: Int)` generates a constructor function named `Point`
        // that accepts `x` and `y` as named args and returns a struct value.
        let span = dt.span;
        let ctor_name = dt.name.clone();
        let field_names: Vec<String> = dt.fields.iter().map(|f| f.name.clone()).collect();
        let arity = field_names.len() as u8;

        // Build a FnProto manually.
        let mut ctor_chunk = Chunk::new();
        let line = span.line;

        // Each parameter is local slot [0], [1], ...
        // Push field name constants and local values onto the stack in pairs,
        // then MakeTypedStruct with the type name.
        for (i, name) in field_names.iter().enumerate() {
            let name_idx = ctor_chunk.add_str(name);
            ctor_chunk.emit_op_u16(OpCode::Const, name_idx, line);
            ctor_chunk.emit_op_u8(OpCode::LoadLocal, i as u8, line);
        }
        let type_name_idx = ctor_chunk.add_str(&ctor_name);
        ctor_chunk.emit_op_u16_u16(OpCode::MakeTypedStruct, type_name_idx, arity as u16, line);
        ctor_chunk.emit_op(OpCode::Return, line);

        let proto = FnProto {
            name: ctor_name.clone(),
            arity,
            chunk: ctor_chunk,
            upvalues: Vec::new(),
        };

        self.emit_const(Constant::FnProto(Box::new(proto)), line);
        let name_idx = self.chunk_mut().add_str(&ctor_name);
        self.emit_u16(OpCode::DefineGlobal, name_idx, line);
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Function compilation helper
    // ─────────────────────────────────────────────────────────────────────────

    fn compile_fn(&mut self, name: String, params: &[Param], body: Block, span: Span) -> FnProto {
        let arity = params.len() as u8;
        self.frames.push(Frame::new(name.clone(), arity));

        // Declare parameters as locals at depth 0.
        let depth = self.frame().scope_depth;
        for param in params {
            self.declare_local(param.internal.clone(), depth);
        }

        // Compile the body.
        self.compile_block_body(body);

        // Ensure there is always a return value.
        let line = span.line;
        self.emit(OpCode::Return, line);

        // Pop the frame.
        let finished = self.frames.pop().unwrap();
        FnProto {
            name,
            arity,
            chunk: finished.chunk,
            upvalues: finished.upvalues,
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Statements
    // ─────────────────────────────────────────────────────────────────────────

    fn compile_stmt(&mut self, stmt: Stmt) {
        match stmt {
            Stmt::Let(s) => self.compile_let(s),
            Stmt::Const(s) => self.compile_const(s),
            Stmt::Return(s) => self.compile_return(s),
            Stmt::Break(s) => self.compile_break(s),
            Stmt::Continue(s) => self.compile_continue(s),
            Stmt::Expr(s) => {
                self.compile_expr(s.expr);
                // Discard the result (expression statement).
                self.emit(OpCode::Pop, s.span.line);
            }
        }
    }

    fn compile_let(&mut self, s: LetStmt) {
        for binding in s.bindings {
            let span = binding.span;
            self.compile_expr(binding.init);
            let depth = self.frame().scope_depth;
            self.declare_local(binding.name, depth);
            // Value is already on the stack in the right slot — no StoreLocal needed.
            let _ = span;
        }
    }

    fn compile_const(&mut self, s: ConstStmt) {
        // `const` is identical to `let` for the bytecode compiler (no mutation
        // enforcement at this stage; that would be a static analysis pass).
        for binding in s.bindings {
            self.compile_expr(binding.init);
            let depth = self.frame().scope_depth;
            self.declare_local(binding.name, depth);
        }
    }

    fn compile_return(&mut self, s: ReturnStmt) {
        match s.value {
            Some(v) => self.compile_expr(*v),
            None => self.emit(OpCode::Null, s.span.line),
        }
        self.emit(OpCode::Return, s.span.line);
    }

    fn compile_break(&mut self, s: BreakStmt) {
        // Push break value (or null).
        match s.value {
            Some(v) => self.compile_expr(*v),
            None => self.emit(OpCode::Null, s.span.line),
        }
        // Find the matching loop context.
        let loop_idx = if let Some(label) = &s.label {
            self.loops
                .iter()
                .rposition(|l| l.label.as_deref() == Some(label.as_str()))
        } else {
            Some(self.loops.len().wrapping_sub(1))
        };

        match loop_idx {
            Some(idx) if idx < self.loops.len() => {
                let patch = self.emit_jump(OpCode::Jump, s.span.line);
                self.loops[idx].break_patches.push(patch);
            }
            _ => {
                self.error("break outside loop", s.span);
            }
        }
    }

    fn compile_continue(&mut self, s: ContinueStmt) {
        let loop_idx = if let Some(label) = &s.label {
            self.loops
                .iter()
                .rposition(|l| l.label.as_deref() == Some(label.as_str()))
        } else {
            Some(self.loops.len().wrapping_sub(1))
        };

        match loop_idx {
            Some(idx) if idx < self.loops.len() => {
                let target = self.loops[idx].loop_start as u16;
                self.emit_u16(OpCode::Loop, target, s.span.line);
            }
            _ => {
                self.error("continue outside loop", s.span);
            }
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Block compilation
    // ─────────────────────────────────────────────────────────────────────────

    /// Compile a block, leaving its tail value on the stack (or `Null`).
    fn compile_block(&mut self, block: Block) {
        self.begin_scope();
        self.compile_block_body(block);
        // end_scope is not called here because the caller controls scope boundaries.
        // The tail value is on the stack; scope cleanup happens above it.
        let line = self.frame().current_line();
        self.end_scope(line);
    }

    /// Compile the contents of a block (statements + optional tail expr).
    ///
    /// Does NOT open/close a scope.
    fn compile_block_body(&mut self, block: Block) {
        for stmt in block.stmts {
            self.compile_stmt(stmt);
        }
        match block.tail {
            Some(tail) => self.compile_expr(*tail),
            None => {
                let line = self.frame().current_line();
                self.emit(OpCode::Null, line);
            }
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Expressions
    // ─────────────────────────────────────────────────────────────────────────

    fn compile_expr(&mut self, expr: Expr) {
        let line = expr.span().line;
        match expr {
            // ── Literals ─────────────────────────────────────────────────────
            Expr::Int(n, _) => match n {
                0 => self.emit(OpCode::Int0, line),
                1 => self.emit(OpCode::Int1, line),
                _ => self.emit_const(Constant::Int(n), line),
            },
            Expr::Float(f, _) => self.emit_const(Constant::Float(f), line),
            Expr::Bool(b, _) => {
                if b {
                    self.emit(OpCode::True, line);
                } else {
                    self.emit(OpCode::False, line);
                }
            }
            Expr::Null(_) => self.emit(OpCode::Null, line),

            // ── String literals ───────────────────────────────────────────────
            Expr::Str(parts, _) => self.compile_str(parts, line),

            // ── Names ─────────────────────────────────────────────────────────
            Expr::Ident(name, span) => self.resolve_name(&name, span),
            Expr::DotIdent(name, span) => {
                // Variant constructor — push as a string constant; the VM
                // creates a tagged value from the dot-ident at runtime.
                let idx = self.chunk_mut().add_str(format!(".{name}"));
                self.emit_u16(OpCode::Const, idx, span.line);
            }
            Expr::Builtin { name, span } => {
                // builtin("name") loads the native function from globals
                // Natives are registered as globals at VM startup
                let idx = self.chunk_mut().add_str(&name);
                self.emit_u16(OpCode::LoadGlobal, idx, span.line);
            }

            // ── Binary operations ─────────────────────────────────────────────
            Expr::Binary { op, lhs, rhs, span } => {
                self.compile_binary(*lhs, op, *rhs, span.line);
            }

            // ── Unary operations ──────────────────────────────────────────────
            Expr::Unary { op, expr, .. } => {
                self.compile_expr(*expr);
                match op {
                    UnOp::Neg => self.emit(OpCode::Neg, line),
                    UnOp::Not => self.emit(OpCode::Not, line),
                }
            }

            // ── Assignment ────────────────────────────────────────────────────
            Expr::Assign {
                target,
                value,
                span,
            } => {
                self.compile_expr(*value);
                self.compile_assign_target(*target, span.line);
            }

            // ── Postfix ───────────────────────────────────────────────────────
            Expr::FieldAccess {
                object,
                field,
                span,
            } => {
                self.compile_expr(*object);
                let name_idx = self.chunk_mut().add_str(&field);
                self.emit_u16(OpCode::GetField, name_idx, span.line);
            }
            Expr::Index {
                object,
                index,
                span,
            } => {
                self.compile_expr(*object);
                self.compile_expr(*index);
                self.emit(OpCode::GetIndex, span.line);
            }
            Expr::SafeNav {
                object,
                field,
                span,
            } => {
                // obj?.field  ≡  if obj == null { null } else { obj.field }
                self.compile_expr(*object);
                self.emit(OpCode::Dup, span.line);
                let jump_null = self.emit_jump(OpCode::JumpIfNull, span.line);
                let name_idx = self.chunk_mut().add_str(&field);
                self.emit_u16(OpCode::GetField, name_idx, span.line);
                let jump_end = self.emit_jump(OpCode::Jump, span.line);
                self.patch_jump(jump_null);
                // stack: null (already there from Dup + JumpIfNull kept value)
                self.patch_jump(jump_end);
            }
            Expr::ForceUnwrap { expr, span } => {
                self.compile_expr(*expr);
                self.emit(OpCode::ForceUnwrap, span.line);
            }
            Expr::PostIncrement { target, span } => {
                self.compile_postfix_mutate(*target, true, span.line);
            }
            Expr::PostDecrement { target, span } => {
                self.compile_postfix_mutate(*target, false, span.line);
            }
            Expr::Cast { expr, ty: _, .. } => {
                // Dynamic typing: cast is a no-op at runtime for now.
                self.compile_expr(*expr);
            }
            Expr::Elvis { left, right, span } => {
                self.compile_expr(*left);
                let patch = self.emit_jump(OpCode::Elvis, span.line);
                self.emit(OpCode::Pop, span.line);
                self.compile_expr(*right);
                self.patch_jump(patch);
            }
            Expr::Range { start, end, span } => {
                // Ranges are represented as two-element tuples at runtime.
                self.compile_expr(*start);
                self.compile_expr(*end);
                self.emit_u16(OpCode::MakeTuple, 2, span.line);
            }

            // ── Calls ─────────────────────────────────────────────────────────
            Expr::Call {
                callee,
                args,
                trailing,
                span,
            } => {
                self.compile_call(*callee, args, trailing, span.line);
            }

            // ── Collections ───────────────────────────────────────────────────
            Expr::List { items, span } => {
                let count = items.len() as u16;
                for item in items {
                    self.compile_collection_item(item);
                }
                self.emit_u16(OpCode::MakeList, count, span.line);
            }
            Expr::Dict { entries, span } => {
                let count = entries.len() as u16;
                for entry in entries {
                    self.compile_expr(entry.key);
                    self.compile_expr(entry.value);
                }
                self.emit_u16(OpCode::MakeDict, count, span.line);
            }
            Expr::Tuple { items, span } => {
                let count = items.len() as u16;
                for item in items {
                    self.compile_collection_item(item);
                }
                self.emit_u16(OpCode::MakeTuple, count, span.line);
            }
            Expr::Struct { fields, span } => {
                let count = fields.len() as u16;
                for field in fields {
                    let name_idx = self.chunk_mut().add_str(&field.name);
                    self.emit_u16(OpCode::Const, name_idx, span.line);
                    self.compile_expr(field.value);
                }
                self.emit_u16(OpCode::MakeStruct, count, span.line);
            }

            // ── Closures ──────────────────────────────────────────────────────
            Expr::Closure(closure) => self.compile_closure(closure),

            // ── Block ─────────────────────────────────────────────────────────
            Expr::Block(block) => self.compile_block(block),

            // ── Control flow ──────────────────────────────────────────────────
            Expr::If(if_expr) => self.compile_if(if_expr),
            Expr::Cases(cases) => self.compile_cases(cases),
            Expr::Loop(loop_expr) => self.compile_loop(loop_expr),
        }
    }

    // ── String compilation ────────────────────────────────────────────────────

    fn compile_str(&mut self, parts: Vec<StringPart>, line: u32) {
        if parts.is_empty() {
            let idx = self.chunk_mut().add_str("");
            self.emit_u16(OpCode::Const, idx, line);
            return;
        }
        if parts.len() == 1 {
            if let StringPart::Raw(s) = &parts[0] {
                let s = s.clone();
                let idx = self.chunk_mut().add_str(s);
                self.emit_u16(OpCode::Const, idx, line);
                return;
            }
        }
        let count = parts.len() as u16;
        for part in parts {
            match part {
                StringPart::Raw(s) => {
                    let idx = self.chunk_mut().add_str(s);
                    self.emit_u16(OpCode::Const, idx, line);
                }
                StringPart::Interp(tokens) => {
                    // Re-parse the interpolated token stream and compile it.
                    let (program_like, _errors) = crate::parser::parse_tokens(tokens);
                    // The interpolation is a single expression; grab the first
                    // expression statement from the synthetic program if available.
                    let expr_opt = program_like.items.into_iter().find_map(|item| {
                        if let Item::Decl(_) = item {
                            None
                        } else {
                            None
                        }
                    });
                    // Fallback: emit null if we can't parse the interpolation.
                    if let Some(expr) = expr_opt {
                        self.compile_expr(expr);
                    } else {
                        self.emit(OpCode::Null, line);
                    }
                }
            }
        }
        self.emit_u16(OpCode::StrConcat, count, line);
    }

    // ── Binary compilation ────────────────────────────────────────────────────

    fn compile_binary(&mut self, lhs: Expr, op: BinOp, rhs: Expr, line: u32) {
        match op {
            // Short-circuit &&
            BinOp::And => {
                self.compile_expr(lhs);
                let patch = self.emit_jump(OpCode::And, line);
                self.emit(OpCode::Pop, line);
                self.compile_expr(rhs);
                self.patch_jump(patch);
            }
            // Short-circuit ||
            BinOp::Or => {
                self.compile_expr(lhs);
                let patch = self.emit_jump(OpCode::Or, line);
                self.emit(OpCode::Pop, line);
                self.compile_expr(rhs);
                self.patch_jump(patch);
            }
            _ => {
                self.compile_expr(lhs);
                self.compile_expr(rhs);
                let instr = match op {
                    BinOp::Add => OpCode::Add,
                    BinOp::Sub => OpCode::Sub,
                    BinOp::Mul => OpCode::Mul,
                    BinOp::Div => OpCode::Div,
                    BinOp::Rem => OpCode::Rem,
                    BinOp::Eq => OpCode::CmpEq,
                    BinOp::Ne => OpCode::CmpNe,
                    BinOp::Lt => OpCode::CmpLt,
                    BinOp::Gt => OpCode::CmpGt,
                    BinOp::Le => OpCode::CmpLe,
                    BinOp::Ge => OpCode::CmpGe,
                    BinOp::And | BinOp::Or => unreachable!(),
                };
                self.emit(instr, line);
            }
        }
    }

    // ── Assignment target ─────────────────────────────────────────────────────

    fn compile_assign_target(&mut self, target: Expr, line: u32) {
        match target {
            Expr::Ident(name, span) => {
                let frame_idx = self.frames.len() - 1;
                if let Some(slot) = self.resolve_local(&name) {
                    self.emit_u8(OpCode::StoreLocal, slot, span.line);
                } else if let Some(uv) = self.resolve_upvalue(&name, frame_idx) {
                    self.emit_u8(OpCode::StoreUpvalue, uv, span.line);
                } else {
                    let name_idx = self.chunk_mut().add_str(&name);
                    self.emit_u16(OpCode::StoreGlobal, name_idx, span.line);
                }
            }
            Expr::FieldAccess {
                object,
                field,
                span,
            } => {
                // value is on stack; we need object below it.
                // Rotate: obj field_name value → store.
                // Compile object first (it goes under the existing value).
                // We need to push the object now and swap.
                // Since value is already on top, compile object second, then swap with Dup/store.
                // Easier: restructure so we compile object first here.
                // Actually at this point the value is already on top of the stack.
                // We emit: compile object, then SetField.
                // But value was already compiled before we called compile_assign_target.
                // Solution: use Dup-like trick by emitting a temporary StoreLocal.
                // For simplicity we compile the object here (it goes on top of value temporarily)
                // then emit SetField which pops object and value and stores.
                // Stack at entry: [... value]
                // After compile object: [... value object]
                // After GetField swapped: [... object value] — need swap
                // Instead: we emit SetField which expects [object value]:
                // We need to swap. Emit Dup to save value, pop value, compile object, ...
                // Most VMs just emit the object before the value.  We're past that.
                // Simple solution: compile object, then swap.
                // Emit a synthetic "swap" using a temp local.
                let tmp_slot = self.frame().locals.len() as u8;
                let depth = self.frame().scope_depth;
                // StoreLocal to tmp (value is on stack).
                self.declare_local("__tmp__", depth);
                self.emit_u8(OpCode::StoreLocal, tmp_slot, span.line);
                // Compile the object.
                self.compile_expr(*object);
                // Reload the value.
                self.emit_u8(OpCode::LoadLocal, tmp_slot, span.line);
                // Pop the tmp local.
                self.frame_mut().locals.pop();
                let name_idx = self.chunk_mut().add_str(&field);
                self.emit_u16(OpCode::SetField, name_idx, line);
            }
            Expr::Index {
                object,
                index,
                span,
            } => {
                let tmp_slot = self.frame().locals.len() as u8;
                let depth = self.frame().scope_depth;
                self.declare_local("__tmp__", depth);
                self.emit_u8(OpCode::StoreLocal, tmp_slot, span.line);
                self.compile_expr(*object);
                self.compile_expr(*index);
                self.emit_u8(OpCode::LoadLocal, tmp_slot, span.line);
                self.frame_mut().locals.pop();
                self.emit(OpCode::SetIndex, line);
            }
            other => {
                self.error("invalid assignment target", other.span());
            }
        }
    }

    // ── Post-increment / decrement ────────────────────────────────────────────

    fn compile_postfix_mutate(&mut self, target: Expr, increment: bool, line: u32) {
        match target {
            Expr::Ident(name, span) => {
                if let Some(slot) = self.resolve_local(&name) {
                    let op = if increment {
                        OpCode::PostInc
                    } else {
                        OpCode::PostDec
                    };
                    self.emit_u8(op, slot, span.line);
                } else {
                    // Global postfix: load, dup, add/sub 1, store, leave old on stack.
                    let name_idx = self.chunk_mut().add_str(&name);
                    self.emit_u16(OpCode::LoadGlobal, name_idx, span.line);
                    self.emit(OpCode::Dup, span.line);
                    self.emit(OpCode::Int1, span.line);
                    self.emit(if increment { OpCode::Add } else { OpCode::Sub }, span.line);
                    self.emit_u16(OpCode::StoreGlobal, name_idx, span.line);
                    // Result: old value is on stack (we Dup'd before mutating).
                }
            }
            other => {
                self.error(
                    "post-increment/decrement requires a simple variable",
                    other.span(),
                );
                self.emit(OpCode::Null, line);
            }
        }
    }

    // ── Collection item ───────────────────────────────────────────────────────

    fn compile_collection_item(&mut self, item: CollectionItem) {
        self.begin_scope();
        for stmt in item.stmts {
            self.compile_stmt(stmt);
        }
        self.compile_expr(item.value);
        let line = self.frame().current_line();
        self.end_scope(line);
    }

    // ── Call ──────────────────────────────────────────────────────────────────

    fn compile_call(
        &mut self,
        callee: Expr,
        args: Vec<Arg>,
        trailing: Vec<TrailingArg>,
        line: u32,
    ) {
        // Check if this is a method call (obj.method(args))
        if let Expr::FieldAccess {
            object,
            field,
            span: _,
        } = callee
        {
            // Method call: compile as CallMethod
            // Stack: ... receiver arg0 arg1 ... argN-1
            self.compile_expr(*object);

            let mut arg_count = args.len();
            for arg in args {
                self.compile_expr(arg.value);
            }

            for trail in trailing {
                arg_count += 1;
                let block_expr = Expr::Block(trail.block.block);
                self.compile_expr(block_expr);
            }

            let method_idx = self.chunk_mut().add_str(&field);
            self.emit_op_u16_u8(OpCode::CallMethod, method_idx, arg_count as u8, line);
            return;
        }

        // Regular call: push callee, then args, then Call
        self.compile_expr(callee);

        let mut arg_count = args.len();
        for arg in args {
            self.compile_expr(arg.value);
        }

        // Push trailing closure arguments.
        for trail in trailing {
            arg_count += 1;
            // Compile the labelled block as a zero-parameter closure.
            let block_expr = Expr::Block(trail.block.block);
            self.compile_expr(block_expr);
        }

        self.emit_u8(OpCode::Call, arg_count as u8, line);
    }

    // ── Closure ───────────────────────────────────────────────────────────────

    fn compile_closure(&mut self, closure: Closure) {
        let span = closure.span;
        // Single-arm closure where the patterns are all Bind or Wildcard.
        // Compile as an anonymous function.
        if closure.arms.len() == 1 {
            let arm = closure.arms.into_iter().next().unwrap();
            let params: Vec<Param> = arm
                .patterns
                .iter()
                .map(|p| match p {
                    Pattern::Bind(n, s) => Param {
                        internal: n.clone(),
                        label: None,
                        ty: None,
                        span: *s,
                    },
                    Pattern::Wildcard(s) => Param {
                        internal: "_".into(),
                        label: None,
                        ty: None,
                        span: *s,
                    },
                    other => Param {
                        internal: "_".into(),
                        label: None,
                        ty: None,
                        span: other.span(),
                    },
                })
                .collect();

            // Build the arm body as a block.
            let body_span = arm.body.span();
            let body_block = Block {
                stmts: Vec::new(),
                tail: Some(Box::new(arm.body)),
                span: body_span,
            };

            let proto = self.compile_fn("<anon>".into(), &params, body_block, span);
            let proto_idx = self
                .chunk_mut()
                .add_constant(Constant::FnProto(Box::new(proto)));
            self.emit_u16(OpCode::Closure, proto_idx, span.line);
        } else {
            // Multi-arm closure: compile as a dispatcher function.
            self.compile_multi_arm_closure(closure);
        }
    }

    fn compile_multi_arm_closure(&mut self, closure: Closure) {
        let span = closure.span;
        let _arm_count = closure.arms.len();
        // Determine arity from the first arm.
        let arity = closure.arms.first().map(|a| a.patterns.len()).unwrap_or(0) as u8;

        // Build a synthetic function: load each arg, pattern-match, jump to body.
        // For now, compile a simplified version that only handles literal and bind patterns.
        self.frames.push(Frame::new("<match>", arity));

        // Parameters: __arg0, __arg1, ...
        let depth = self.frame().scope_depth;
        for i in 0..arity {
            self.declare_local(format!("__arg{i}"), depth);
        }

        let mut end_patches: Vec<usize> = Vec::new();

        for arm in closure.arms {
            let arm_line = arm.span.line;
            let mut fail_patches: Vec<usize> = Vec::new();

            // Compile pattern checks.
            for (i, pattern) in arm.patterns.iter().enumerate() {
                match pattern {
                    Pattern::Wildcard(_) | Pattern::Bind(_, _) => {
                        // Always matches; bind is handled below.
                    }
                    Pattern::Literal(lit_expr) => {
                        // Compare arg[i] == literal.
                        self.emit_u8(OpCode::LoadLocal, i as u8, arm_line);
                        self.compile_expr(lit_expr.clone());
                        self.emit(OpCode::CmpEq, arm_line);
                        let patch = self.emit_jump(OpCode::JumpIfFalse, arm_line);
                        self.emit(OpCode::Pop, arm_line);
                        fail_patches.push(patch);
                    }
                    Pattern::Variant {
                        name,
                        inner: _,
                        span: _,
                    } => {
                        // Check if arg[i] is a struct with type_name == name.
                        self.emit_u8(OpCode::LoadLocal, i as u8, arm_line);
                        self.emit(OpCode::GetTag, arm_line);
                        let name_idx = self.chunk_mut().add_str(name);
                        self.emit_u16(OpCode::Const, name_idx, arm_line);
                        self.emit(OpCode::CmpEq, arm_line);
                        let patch = self.emit_jump(OpCode::JumpIfFalse, arm_line);
                        self.emit(OpCode::Pop, arm_line);
                        fail_patches.push(patch);
                    }
                    Pattern::Tuple(_, _) => {
                        // Tuple patterns not yet implemented; skip.
                    }
                }
            }

            // Compile guard if present.
            if let Some(guard) = arm.guard {
                // Bind args first so guard can reference them.
                let guard_line = guard.span().line;
                self.compile_expr(guard);
                let patch = self.emit_jump(OpCode::JumpIfFalse, guard_line);
                self.emit(OpCode::Pop, guard_line);
                fail_patches.push(patch);
            }

            // Bind pattern variables.
            for (i, pattern) in arm.patterns.iter().enumerate() {
                match pattern {
                    Pattern::Bind(name, _span) => {
                        // LoadLocal arg[i] → stays on stack as the local.
                        self.emit_u8(OpCode::LoadLocal, i as u8, arm_line);
                        let depth = self.frame().scope_depth;
                        self.declare_local(name.clone(), depth);
                    }
                    Pattern::Variant {
                        inner: Some(inner_pat),
                        ..
                    } => {
                        // Extract inner value and bind if needed.
                        match inner_pat.as_ref() {
                            Pattern::Bind(name, _) => {
                                // LoadLocal arg[i], then GetField "value" to extract inner.
                                self.emit_u8(OpCode::LoadLocal, i as u8, arm_line);
                                let value_idx = self.chunk_mut().add_str("value");
                                self.emit_u16(OpCode::GetField, value_idx, arm_line);
                                let depth = self.frame().scope_depth;
                                self.declare_local(name.clone(), depth);
                            }
                            Pattern::Wildcard(_) => {
                                // Matched but no binding needed.
                            }
                            _ => {
                                // Nested patterns inside variants not yet supported.
                            }
                        }
                    }
                    _ => {}
                }
            }

            // Compile arm body.
            let body_line = arm.body.span().line;
            self.compile_expr(arm.body);
            let end_patch = self.emit_jump(OpCode::Jump, body_line);
            end_patches.push(end_patch);

            // Patch all failure jumps to here.
            for patch in fail_patches {
                self.patch_jump(patch);
                self.emit(OpCode::Pop, arm_line); // pop the false boolean
            }
        }

        // If no arm matched, return null.
        let final_line = span.line;
        self.emit(OpCode::Null, final_line);

        // Patch all end jumps.
        for patch in end_patches {
            self.patch_jump(patch);
        }
        self.emit(OpCode::Return, final_line);

        let finished = self.frames.pop().unwrap();
        let proto = FnProto {
            name: "<match>".into(),
            arity,
            chunk: finished.chunk,
            upvalues: finished.upvalues,
        };
        let proto_idx = self
            .chunk_mut()
            .add_constant(Constant::FnProto(Box::new(proto)));
        self.emit_u16(OpCode::Closure, proto_idx, span.line);
    }

    // ── If ────────────────────────────────────────────────────────────────────

    fn compile_if(&mut self, if_expr: IfExpr) {
        let line = if_expr.span.line;
        self.compile_expr(*if_expr.condition);
        let else_jump = self.emit_jump(OpCode::JumpIfFalse, line);
        self.emit(OpCode::Pop, line); // pop condition

        self.compile_block(if_expr.then_block);

        match if_expr.else_block {
            Some(else_block) => {
                let end_jump = self.emit_jump(OpCode::Jump, line);
                self.patch_jump(else_jump);
                self.emit(OpCode::Pop, line); // pop condition
                self.compile_block(else_block);
                self.patch_jump(end_jump);
            }
            None => {
                let end_jump = self.emit_jump(OpCode::Jump, line);
                self.patch_jump(else_jump);
                self.emit(OpCode::Pop, line); // pop condition
                self.emit(OpCode::Null, line); // if without else yields null
                self.patch_jump(end_jump);
            }
        }
    }

    // ── Cases ─────────────────────────────────────────────────────────────────

    fn compile_cases(&mut self, cases: CasesExpr) {
        let line = cases.span.line;
        let mut end_patches: Vec<usize> = Vec::new();

        for arm in cases.arms {
            let arm_line = arm.span.line;
            self.compile_expr(arm.guard);
            let skip = self.emit_jump(OpCode::JumpIfFalse, arm_line);
            self.emit(OpCode::Pop, arm_line);
            self.compile_expr(arm.body);
            let end = self.emit_jump(OpCode::Jump, arm_line);
            end_patches.push(end);
            self.patch_jump(skip);
            self.emit(OpCode::Pop, arm_line);
        }

        // Default: null.
        self.emit(OpCode::Null, line);

        for patch in end_patches {
            self.patch_jump(patch);
        }
    }

    // ── Loop ──────────────────────────────────────────────────────────────────

    fn compile_loop(&mut self, loop_expr: LoopExpr) {
        let line = loop_expr.span.line;
        let label = loop_expr.body.label.clone();
        let loop_start = self.chunk_mut().current_offset();

        self.loops.push(LoopCtx {
            label,
            loop_start,
            break_patches: Vec::new(),
        });

        match loop_expr.condition {
            None => {
                // Indefinite loop.
                self.begin_scope();
                self.compile_block_body(loop_expr.body.block);
                self.emit(OpCode::Pop, line); // discard body value
                let end_scope_line = self.frame().current_line();
                self.end_scope(end_scope_line);
                // Jump back to start.
                self.emit_u16(OpCode::Loop, loop_start as u16, line);
            }
            Some(cond_block) => {
                // Conditional loop: `loop while { cond } do { body }`.
                let cond_start = self.chunk_mut().current_offset();
                // Re-evaluate condition each iteration.
                self.compile_block(cond_block);
                let exit_jump = self.emit_jump(OpCode::JumpIfFalse, line);
                self.emit(OpCode::Pop, line);
                self.begin_scope();
                self.compile_block_body(loop_expr.body.block);
                self.emit(OpCode::Pop, line);
                let end_scope_line = self.frame().current_line();
                self.end_scope(end_scope_line);
                self.emit_u16(OpCode::Loop, cond_start as u16, line);
                self.patch_jump(exit_jump);
                self.emit(OpCode::Pop, line); // pop false condition
                self.emit(OpCode::Null, line); // loop result = null
            }
        }

        // Patch break jumps.
        let loop_ctx = self.loops.pop().unwrap();
        let after = self.chunk_mut().current_offset();
        for patch in loop_ctx.break_patches {
            self.chunk_mut().code[patch] = ((after >> 8) & 0xFF) as u8;
            self.chunk_mut().code[patch + 1] = (after & 0xFF) as u8;
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Pattern helper
// ─────────────────────────────────────────────────────────────────────────────

impl Pattern {
    fn span(&self) -> Span {
        match self {
            Pattern::Wildcard(s) => *s,
            Pattern::Literal(e) => e.span(),
            Pattern::Bind(_, s) => *s,
            Pattern::Tuple(_, s) => *s,
            Pattern::Variant { span, .. } => *span,
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Public entry point
// ─────────────────────────────────────────────────────────────────────────────

/// Compile an [`ast::Program`] to a module-level [`Chunk`].
pub fn compile(program: Program) -> Result<Chunk, CompileError> {
    let compiler = Compiler::new();
    compiler
        .compile_program(program)
        .map_err(|mut errs| errs.remove(0))
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::lex;
    use crate::parser::parse_tokens;

    fn compile_src(src: &str) -> Chunk {
        let (tokens, lex_errs) = lex(src);
        assert!(lex_errs.is_empty(), "lex errors: {lex_errs:?}");
        let (program, parse_errs) = parse_tokens(tokens);
        assert!(parse_errs.is_empty(), "parse errors: {parse_errs:?}");
        compile(program).expect("compile error")
    }

    #[test]
    fn test_compile_integer_literal() {
        let chunk = compile_src("def x = 42; defn main() {}");
        // Should have at least a Const and DefineGlobal.
        assert!(!chunk.code.is_empty());
    }

    #[test]
    fn test_compile_arithmetic() {
        let chunk = compile_src("def y = 1 + 2; defn main() {}");
        assert!(!chunk.code.is_empty());
    }

    #[test]
    fn test_compile_defn() {
        let chunk = compile_src("defn add(a, b) { a + b } defn main() {}");
        assert!(!chunk.code.is_empty());
    }
}
