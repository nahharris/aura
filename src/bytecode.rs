//! Bytecode representation for the Aura virtual machine.
//!
//! A compiled Aura function is represented as a [`Chunk`]: a flat `Vec<u8>`
//! of instructions (encoded as raw bytes), a constant pool, and a line-number
//! table for stack traces.
//!
//! # Encoding
//!
//! Each instruction is encoded as one or more bytes:
//! - The first byte is the [`OpCode`] discriminant.
//! - Operands immediately follow, in big-endian order.
//!
//! Operand sizes:
//! - **u8** — used for small constant indices (0..=255).
//! - **u16** — used for jump offsets and larger constant pool indices.
//!
//! All jumps store the *absolute* bytecode offset of the target instruction.

use std::fmt;

// ─────────────────────────────────────────────────────────────────────────────
// OpCode
// ─────────────────────────────────────────────────────────────────────────────

/// Every instruction the Aura VM can execute.
///
/// The `#[repr(u8)]` attribute ensures each variant fits in one byte.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum OpCode {
    // ── Constants / literals ─────────────────────────────────────────────────
    /// Push a value from the constant pool onto the stack.
    /// Operand: u16 — constant pool index.
    Const = 0x01,
    /// Push the integer 0 (shorthand to avoid a constant pool entry).
    Int0 = 0x02,
    /// Push the integer 1.
    Int1 = 0x03,
    /// Push `true`.
    True = 0x04,
    /// Push `false`.
    False = 0x05,
    /// Push `null`.
    Null = 0x06,

    // ── Stack manipulation ────────────────────────────────────────────────────
    /// Discard the top stack value.
    Pop = 0x10,
    /// Duplicate the top stack value.
    Dup = 0x11,

    // ── Local variables ───────────────────────────────────────────────────────
    /// Load a local variable onto the stack.
    /// Operand: u8 — slot index in the current call frame.
    LoadLocal = 0x20,
    /// Store the top of the stack into a local variable slot (pops the value).
    /// Operand: u8 — slot index.
    StoreLocal = 0x21,

    // ── Upvalues (closed-over variables) ─────────────────────────────────────
    /// Load an upvalue.
    /// Operand: u8 — upvalue index in the closure object.
    LoadUpvalue = 0x22,
    /// Store the top of stack into an upvalue (pops the value).
    /// Operand: u8 — upvalue index.
    StoreUpvalue = 0x23,
    /// Close over the given local variable by moving it onto the heap.
    /// Operand: u8 — slot index to close.
    CloseUpvalue = 0x24,

    // ── Globals ───────────────────────────────────────────────────────────────
    /// Load a global variable by name.
    /// Operand: u16 — constant pool index of the name string.
    LoadGlobal = 0x25,
    /// Define (or redefine) a global variable.
    /// Operand: u16 — constant pool index of the name string.
    DefineGlobal = 0x26,
    /// Store into an existing global variable.
    /// Operand: u16 — constant pool index of the name string.
    StoreGlobal = 0x27,

    // ── Arithmetic ────────────────────────────────────────────────────────────
    /// Integer / float addition.
    Add = 0x30,
    /// Subtraction.
    Sub = 0x31,
    /// Multiplication.
    Mul = 0x32,
    /// Division (float if either operand is float).
    Div = 0x33,
    /// Remainder.
    Rem = 0x34,
    /// Arithmetic negation.
    Neg = 0x35,

    // ── Comparison ────────────────────────────────────────────────────────────
    /// `==`
    CmpEq = 0x40,
    /// `!=`
    CmpNe = 0x41,
    /// `<`
    CmpLt = 0x42,
    /// `>`
    CmpGt = 0x43,
    /// `<=`
    CmpLe = 0x44,
    /// `>=`
    CmpGe = 0x45,

    // ── Logic ─────────────────────────────────────────────────────────────────
    /// Boolean NOT (`!`).
    Not = 0x50,
    /// Short-circuit AND — if top is falsy, jump to operand address without
    /// evaluating RHS.  Operand: u16 jump target.
    And = 0x51,
    /// Short-circuit OR.  Operand: u16 jump target.
    Or = 0x52,

    // ── Control flow ──────────────────────────────────────────────────────────
    /// Unconditional jump.  Operand: u16 target offset.
    Jump = 0x60,
    /// Jump if the top of stack is falsy (pops the value).
    /// Operand: u16 target offset.
    JumpIfFalse = 0x61,
    /// Jump if the top of stack is truthy (pops the value).
    /// Operand: u16 target offset.
    JumpIfTrue = 0x62,
    /// Jump if the top of stack is null (pops the value).
    /// Operand: u16 target offset.
    JumpIfNull = 0x63,
    /// Loop back: unconditional jump used at the end of loop bodies.
    /// Operand: u16 target offset (usually lower than current ip).
    Loop = 0x64,

    // ── Calls and returns ─────────────────────────────────────────────────────
    /// Call a callable value.
    /// Operand: u8 — number of arguments on the stack above the callee.
    Call = 0x70,
    /// Return the top of stack from the current function, popping the call frame.
    Return = 0x71,
    /// Call a native (Rust) function.
    /// Operand: u8 — native function index in the VM's builtins table.
    CallNative = 0x72,
    /// Tail call optimisation: reuse current call frame.
    /// Operand: u8 — argument count.
    TailCall = 0x73,
    /// Call a method on the receiver.
    /// Stack: ... receiver arg0 arg1 ... argN-1
    /// Operand: u16 — constant pool index of method name string.
    /// Operand: u8 — argument count (NOT including receiver).
    /// Resolves to "Type.method" global at runtime based on receiver's type.
    CallMethod = 0x74,

    // ── Closures ──────────────────────────────────────────────────────────────
    /// Create a closure object from a function prototype in the constant pool.
    /// Operand: u16 — constant pool index of the `FnProto`.
    Closure = 0x80,

    // ── Collections ───────────────────────────────────────────────────────────
    /// Build a list from the top N stack values (pushed left-to-right).
    /// Operand: u16 — item count.
    MakeList = 0x90,
    /// Build a dict from the top N*2 stack values (key₀, val₀, key₁, val₁ …).
    /// Operand: u16 — entry count (NOT item count; item count = N*2).
    MakeDict = 0x91,
    /// Build a tuple from the top N stack values.
    /// Operand: u16 — item count.
    MakeTuple = 0x92,
    /// Build a struct from the top N*2 stack values (name_idx, val pairs).
    /// Operand: u16 — field count.
    MakeStruct = 0x93,
    /// Build a typed struct (from deftype) with a type_name.
    /// Operand: u16 type_name_idx, u16 field_count.
    MakeTypedStruct = 0x94,

    // ── Field / index access ──────────────────────────────────────────────────
    /// Load a named field from the object on top of the stack.
    /// Operand: u16 — constant pool index of the field name string.
    GetField = 0xa0,
    /// Store a value into a named field.
    /// Stack: … object value → … ; operand: u16 field name index.
    SetField = 0xa1,
    /// Load by index: `object[index]`.
    /// Stack: … object index → … value.
    GetIndex = 0xa2,
    /// Store by index: `object[index] = value`.
    /// Stack: … object index value → …
    SetIndex = 0xa3,

    // ── String interpolation ──────────────────────────────────────────────────
    /// Concatenate N string-coerced values into one string.
    /// Operand: u16 — count of values to concatenate.
    StrConcat = 0xb0,

    // ── Miscellaneous ─────────────────────────────────────────────────────────
    /// Coerce the top of stack to a boolean (truthiness check) — replaces.
    ToBool = 0xc0,
    /// Force-unwrap: panic if top of stack is null.
    ForceUnwrap = 0xc1,
    /// Post-increment: load, push old value, store incremented value.
    /// Operand: u8 local slot.
    PostInc = 0xc2,
    /// Post-decrement.
    /// Operand: u8 local slot.
    PostDec = 0xc3,
    /// Elvis operator: if top of stack is non-null, jump past the RHS.
    /// Operand: u16 — jump-past-RHS offset.
    Elvis = 0xc4,
    /// Get the variant tag of a struct (its type_name field).
    /// Pops top of stack, pushes the tag string (or "" for non-structs).
    GetTag = 0xc5,

    /// No-operation (used as a placeholder during patching).
    Nop = 0xff,
}

impl TryFrom<u8> for OpCode {
    type Error = u8;
    fn try_from(byte: u8) -> Result<Self, Self::Error> {
        // Safety: the match is exhaustive over all defined opcodes.
        match byte {
            0x01 => Ok(OpCode::Const),
            0x02 => Ok(OpCode::Int0),
            0x03 => Ok(OpCode::Int1),
            0x04 => Ok(OpCode::True),
            0x05 => Ok(OpCode::False),
            0x06 => Ok(OpCode::Null),
            0x10 => Ok(OpCode::Pop),
            0x11 => Ok(OpCode::Dup),
            0x20 => Ok(OpCode::LoadLocal),
            0x21 => Ok(OpCode::StoreLocal),
            0x22 => Ok(OpCode::LoadUpvalue),
            0x23 => Ok(OpCode::StoreUpvalue),
            0x24 => Ok(OpCode::CloseUpvalue),
            0x25 => Ok(OpCode::LoadGlobal),
            0x26 => Ok(OpCode::DefineGlobal),
            0x27 => Ok(OpCode::StoreGlobal),
            0x30 => Ok(OpCode::Add),
            0x31 => Ok(OpCode::Sub),
            0x32 => Ok(OpCode::Mul),
            0x33 => Ok(OpCode::Div),
            0x34 => Ok(OpCode::Rem),
            0x35 => Ok(OpCode::Neg),
            0x40 => Ok(OpCode::CmpEq),
            0x41 => Ok(OpCode::CmpNe),
            0x42 => Ok(OpCode::CmpLt),
            0x43 => Ok(OpCode::CmpGt),
            0x44 => Ok(OpCode::CmpLe),
            0x45 => Ok(OpCode::CmpGe),
            0x50 => Ok(OpCode::Not),
            0x51 => Ok(OpCode::And),
            0x52 => Ok(OpCode::Or),
            0x60 => Ok(OpCode::Jump),
            0x61 => Ok(OpCode::JumpIfFalse),
            0x62 => Ok(OpCode::JumpIfTrue),
            0x63 => Ok(OpCode::JumpIfNull),
            0x64 => Ok(OpCode::Loop),
            0x70 => Ok(OpCode::Call),
            0x71 => Ok(OpCode::Return),
            0x72 => Ok(OpCode::CallNative),
            0x73 => Ok(OpCode::TailCall),
            0x74 => Ok(OpCode::CallMethod),
            0x80 => Ok(OpCode::Closure),
            0x90 => Ok(OpCode::MakeList),
            0x91 => Ok(OpCode::MakeDict),
            0x92 => Ok(OpCode::MakeTuple),
            0x93 => Ok(OpCode::MakeStruct),
            0x94 => Ok(OpCode::MakeTypedStruct),
            0xa0 => Ok(OpCode::GetField),
            0xa1 => Ok(OpCode::SetField),
            0xa2 => Ok(OpCode::GetIndex),
            0xa3 => Ok(OpCode::SetIndex),
            0xb0 => Ok(OpCode::StrConcat),
            0xc0 => Ok(OpCode::ToBool),
            0xc1 => Ok(OpCode::ForceUnwrap),
            0xc2 => Ok(OpCode::PostInc),
            0xc3 => Ok(OpCode::PostDec),
            0xc4 => Ok(OpCode::Elvis),
            0xc5 => Ok(OpCode::GetTag),
            0xff => Ok(OpCode::Nop),
            other => Err(other),
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Constant pool value
// ─────────────────────────────────────────────────────────────────────────────

/// A compile-time constant that lives in the [`Chunk`]'s constant pool.
///
/// These are distinct from runtime [`crate::value::Value`]s: they are
/// immutable, do not participate in GC, and can be stored in `Vec<Constant>`.
#[derive(Debug, Clone, PartialEq)]
pub enum Constant {
    /// A 64-bit integer literal.
    Int(i64),
    /// A 64-bit float literal.
    Float(f64),
    /// A string literal (UTF-8, owned).
    Str(String),
    /// A boolean literal.
    Bool(bool),
    /// The null literal.
    Null,
    /// A compiled function prototype (inner chunk + metadata).
    FnProto(Box<FnProto>),
}

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constant::Int(n) => write!(f, "{n}"),
            Constant::Float(n) => write!(f, "{n}"),
            Constant::Str(s) => write!(f, "{s:?}"),
            Constant::Bool(b) => write!(f, "{b}"),
            Constant::Null => write!(f, "null"),
            Constant::FnProto(p) => write!(f, "<fn {}>", p.name),
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Function prototype
// ─────────────────────────────────────────────────────────────────────────────

/// A compiled function prototype: its bytecode, arity, upvalue descriptors, and metadata.
///
/// `FnProto` is stored as a `Constant::FnProto` in the enclosing chunk's
/// constant pool.  At runtime, wrapping it in a closure object captures the
/// live upvalues.
#[derive(Debug, Clone, PartialEq)]
pub struct FnProto {
    /// The function's declared name (for stack traces; `"<anon>"` for closures).
    pub name: String,
    /// Number of parameters (arity).
    pub arity: u8,
    /// The function's bytecode and constants.
    pub chunk: Chunk,
    /// Upvalue descriptors: for each upvalue, whether it captures a local in
    /// the immediately enclosing scope (`is_local = true`) or an upvalue of
    /// the enclosing closure (`is_local = false`), and its index.
    pub upvalues: Vec<UpvalueDesc>,
}

/// Describes one captured variable in a closure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UpvalueDesc {
    /// `true` if this upvalue captures a local variable in the immediately
    /// enclosing scope; `false` if it re-captures an upvalue from that scope.
    pub is_local: bool,
    /// The slot index (if `is_local`) or upvalue index (if `!is_local`) in
    /// the enclosing scope.
    pub index: u8,
}

// ─────────────────────────────────────────────────────────────────────────────
// Chunk
// ─────────────────────────────────────────────────────────────────────────────

/// A bytecode chunk: the compiled form of one function (or the module top level).
///
/// The VM executes a `Chunk` inside a [`crate::vm::CallFrame`].
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Chunk {
    /// Raw instruction bytes.
    pub code: Vec<u8>,
    /// Constant pool; indexed by u16.
    pub constants: Vec<Constant>,
    /// Source line for each byte in `code` (parallel to `code`).
    /// Used for stack traces and error messages.
    pub lines: Vec<u32>,
}

impl Chunk {
    /// Create an empty chunk.
    pub fn new() -> Self {
        Self::default()
    }

    // ── Emission helpers ─────────────────────────────────────────────────────

    /// Emit a single byte (raw opcode or operand).
    #[inline]
    pub fn emit_byte(&mut self, byte: u8, line: u32) {
        self.code.push(byte);
        self.lines.push(line);
    }

    /// Emit an opcode byte.
    #[inline]
    pub fn emit_op(&mut self, op: OpCode, line: u32) {
        self.emit_byte(op as u8, line);
    }

    /// Emit a u16 operand as two bytes, big-endian.
    #[inline]
    pub fn emit_u16(&mut self, value: u16, line: u32) {
        let [hi, lo] = value.to_be_bytes();
        self.emit_byte(hi, line);
        self.emit_byte(lo, line);
    }

    /// Emit an opcode followed by a u16 operand.
    #[inline]
    pub fn emit_op_u16(&mut self, op: OpCode, operand: u16, line: u32) {
        self.emit_op(op, line);
        self.emit_u16(operand, line);
    }

    /// Emit an opcode followed by a u8 operand.
    #[inline]
    pub fn emit_op_u8(&mut self, op: OpCode, operand: u8, line: u32) {
        self.emit_op(op, line);
        self.emit_byte(operand, line);
    }

    /// Emit an opcode followed by a u16 operand and then a u8 operand.
    #[inline]
    pub fn emit_op_u16_u8(&mut self, op: OpCode, operand_u16: u16, operand_u8: u8, line: u32) {
        self.emit_op(op, line);
        self.emit_u16(operand_u16, line);
        self.emit_byte(operand_u8, line);
    }

    /// Emit an opcode followed by two u16 operands.
    #[inline]
    pub fn emit_op_u16_u16(&mut self, op: OpCode, operand1: u16, operand2: u16, line: u32) {
        self.emit_op(op, line);
        self.emit_u16(operand1, line);
        self.emit_u16(operand2, line);
    }

    // ── Constant pool ────────────────────────────────────────────────────────

    /// Add a constant to the pool and return its index.
    ///
    /// If the exact constant already exists in the pool, the existing index is
    /// returned (deduplication).
    pub fn add_constant(&mut self, c: Constant) -> u16 {
        // Deduplicate simple constants.
        if let Some(idx) = self.constants.iter().position(|x| x == &c) {
            return idx as u16;
        }
        let idx = self.constants.len();
        assert!(idx < 0x1_0000, "constant pool overflow");
        self.constants.push(c);
        idx as u16
    }

    /// Convenience: add a string constant and return its pool index.
    pub fn add_str(&mut self, s: impl Into<String>) -> u16 {
        self.add_constant(Constant::Str(s.into()))
    }

    /// Emit `OpCode::Const <u16 index>` for the given constant.
    pub fn emit_const(&mut self, c: Constant, line: u32) {
        let idx = self.add_constant(c);
        self.emit_op_u16(OpCode::Const, idx, line);
    }

    // ── Jump patching ────────────────────────────────────────────────────────

    /// Emit a jump instruction with a placeholder target (`0xFFFF`).
    /// Returns the byte offset of the u16 operand so it can be patched later.
    pub fn emit_jump(&mut self, op: OpCode, line: u32) -> usize {
        self.emit_op(op, line);
        let patch_offset = self.code.len();
        self.emit_byte(0xFF, line);
        self.emit_byte(0xFF, line);
        patch_offset
    }

    /// Patch a previously-emitted jump operand to point to the current
    /// end of the code vector.
    pub fn patch_jump(&mut self, patch_offset: usize) {
        let target = self.code.len() as u16;
        let [hi, lo] = target.to_be_bytes();
        self.code[patch_offset] = hi;
        self.code[patch_offset + 1] = lo;
    }

    // ── Utilities ────────────────────────────────────────────────────────────

    /// Return the current write position (= next instruction offset).
    #[inline]
    pub fn current_offset(&self) -> usize {
        self.code.len()
    }

    /// Read a u16 from `code[offset]` (big-endian).
    #[inline]
    pub fn read_u16(&self, offset: usize) -> u16 {
        u16::from_be_bytes([self.code[offset], self.code[offset + 1]])
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Disassembler
// ─────────────────────────────────────────────────────────────────────────────

/// Disassemble `chunk` to a human-readable string.
///
/// This is used for debugging the compiler output; it is not used in normal
/// execution.
pub fn disassemble(chunk: &Chunk, name: &str) -> String {
    let mut out = format!("=== {name} ===\n");
    let mut offset = 0usize;
    while offset < chunk.code.len() {
        let (s, size) = disassemble_instruction(chunk, offset);
        let line = chunk.lines.get(offset).copied().unwrap_or(0);
        out.push_str(&format!("{offset:04x}  [{line:4}]  {s}\n"));
        offset += size;
    }
    out
}

/// Disassemble a single instruction at `offset`.
///
/// Returns `(text, bytes_consumed)`.
pub fn disassemble_instruction(chunk: &Chunk, offset: usize) -> (String, usize) {
    let byte = chunk.code[offset];
    let op = match OpCode::try_from(byte) {
        Ok(op) => op,
        Err(_) => return (format!("UNKNOWN({byte:#04x})"), 1),
    };

    match op {
        // no operands
        OpCode::Int0
        | OpCode::Int1
        | OpCode::True
        | OpCode::False
        | OpCode::Null
        | OpCode::Pop
        | OpCode::Dup
        | OpCode::Add
        | OpCode::Sub
        | OpCode::Mul
        | OpCode::Div
        | OpCode::Rem
        | OpCode::Neg
        | OpCode::CmpEq
        | OpCode::CmpNe
        | OpCode::CmpLt
        | OpCode::CmpGt
        | OpCode::CmpLe
        | OpCode::CmpGe
        | OpCode::Not
        | OpCode::Return
        | OpCode::ToBool
        | OpCode::ForceUnwrap
        | OpCode::GetTag
        | OpCode::GetIndex
        | OpCode::SetIndex
        | OpCode::Nop => (format!("{op:?}"), 1),

        // u8 operand
        OpCode::LoadLocal
        | OpCode::StoreLocal
        | OpCode::LoadUpvalue
        | OpCode::StoreUpvalue
        | OpCode::CloseUpvalue
        | OpCode::Call
        | OpCode::CallNative
        | OpCode::TailCall
        | OpCode::PostInc
        | OpCode::PostDec => {
            let operand = chunk.code.get(offset + 1).copied().unwrap_or(0);
            (format!("{op:?} {operand}"), 2)
        }

        // u16 + u8 operands — CallMethod: method name + arg count
        OpCode::CallMethod => {
            let idx = chunk.read_u16(offset + 1);
            let arg_count = chunk.code.get(offset + 3).copied().unwrap_or(0);
            let name = chunk
                .constants
                .get(idx as usize)
                .map(|c| c.to_string())
                .unwrap_or_else(|| "<oob>".to_string());
            (format!("{op:?} {name} ({arg_count} args)"), 4)
        }

        // u16 operand — generic display
        OpCode::Const | OpCode::Closure => {
            let idx = chunk.read_u16(offset + 1);
            let c = chunk
                .constants
                .get(idx as usize)
                .map(|c| c.to_string())
                .unwrap_or_else(|| "<oob>".to_string());
            (format!("{op:?} [{idx}] = {c}"), 3)
        }

        // u16 operand — global name
        OpCode::LoadGlobal | OpCode::DefineGlobal | OpCode::StoreGlobal => {
            let idx = chunk.read_u16(offset + 1);
            let name = chunk
                .constants
                .get(idx as usize)
                .map(|c| c.to_string())
                .unwrap_or_else(|| "<oob>".to_string());
            (format!("{op:?} {name}"), 3)
        }

        // u16 operand — jump target
        OpCode::Jump
        | OpCode::JumpIfFalse
        | OpCode::JumpIfTrue
        | OpCode::JumpIfNull
        | OpCode::Loop
        | OpCode::And
        | OpCode::Or
        | OpCode::Elvis => {
            let target = chunk.read_u16(offset + 1);
            (format!("{op:?} -> {target:#06x}"), 3)
        }

        // u16 operand — field name
        OpCode::GetField | OpCode::SetField => {
            let idx = chunk.read_u16(offset + 1);
            let name = chunk
                .constants
                .get(idx as usize)
                .map(|c| c.to_string())
                .unwrap_or_else(|| "<oob>".to_string());
            (format!("{op:?} {name}"), 3)
        }

        // u16 operand — count
        OpCode::MakeList
        | OpCode::MakeDict
        | OpCode::MakeTuple
        | OpCode::MakeStruct
        | OpCode::StrConcat => {
            let count = chunk.read_u16(offset + 1);
            (format!("{op:?} count={count}"), 3)
        }

        // u16 + u16 operands — MakeTypedStruct: type_name_idx + field_count
        OpCode::MakeTypedStruct => {
            let type_name_idx = chunk.read_u16(offset + 1);
            let field_count = chunk.read_u16(offset + 3);
            let type_name = chunk
                .constants
                .get(type_name_idx as usize)
                .map(|c| c.to_string())
                .unwrap_or_else(|| "<oob>".to_string());
            (format!("{op:?} {type_name} fields={field_count}"), 5)
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_opcode_roundtrip() {
        for byte in [0x01u8, 0x30, 0x70, 0xa0, 0xff] {
            let op = OpCode::try_from(byte).unwrap();
            assert_eq!(op as u8, byte);
        }
        assert!(OpCode::try_from(0x99u8).is_err());
    }

    #[test]
    fn test_chunk_emit_and_read() {
        let mut chunk = Chunk::new();
        chunk.emit_op(OpCode::Int1, 1);
        chunk.emit_op(OpCode::Int1, 1);
        chunk.emit_op(OpCode::Add, 1);
        chunk.emit_op(OpCode::Return, 1);
        assert_eq!(chunk.code.len(), 4);
        assert_eq!(chunk.code[0], OpCode::Int1 as u8);
    }

    #[test]
    fn test_constant_dedup() {
        let mut chunk = Chunk::new();
        let i1 = chunk.add_constant(Constant::Int(42));
        let i2 = chunk.add_constant(Constant::Int(42));
        let i3 = chunk.add_constant(Constant::Int(99));
        assert_eq!(i1, i2, "duplicate constants should share an index");
        assert_ne!(i1, i3);
        assert_eq!(chunk.constants.len(), 2);
    }

    #[test]
    fn test_jump_patch() {
        let mut chunk = Chunk::new();
        let patch = chunk.emit_jump(OpCode::JumpIfFalse, 1);
        chunk.emit_op(OpCode::Pop, 1);
        chunk.patch_jump(patch);
        let target = chunk.read_u16(patch);
        assert_eq!(target as usize, chunk.code.len());
    }

    #[test]
    fn test_disassemble_smoke() {
        let mut chunk = Chunk::new();
        chunk.emit_const(Constant::Int(42), 1);
        chunk.emit_op(OpCode::Return, 1);
        let text = disassemble(&chunk, "test");
        assert!(text.contains("Const"));
        assert!(text.contains("Return"));
    }
}
