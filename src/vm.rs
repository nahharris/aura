//! The Aura virtual machine.
//!
//! The VM is a **stack-based interpreter** that executes [`Chunk`] bytecode.
//! It maintains a call stack of [`CallFrame`]s and a flat value stack.
//!
//! # Execution model
//!
//! - The value stack is a `Vec<Value>` shared across all call frames.
//! - Each [`CallFrame`] stores its own `ip` (instruction pointer), a pointer
//!   to the closure being executed, and the `stack_base` — the index in the
//!   shared value stack where this frame's locals begin.
//! - On `Call`, a new frame is pushed; on `Return`, the frame is popped and
//!   the return value is left on top of the stack.
//!
//! # GC integration
//!
//! The VM drives GC collection by calling [`GcHeap::collect`] when the heap
//! exceeds its threshold.  All live `Value`s on the stack and in the globals
//! table are treated as roots.

use std::collections::HashMap;

use crate::bytecode::{Chunk, Constant, FnProto, OpCode};
use crate::gc::GcHeap;
use crate::value::{NativeFn, ObjClosure, Upvalue, Value};

// ─────────────────────────────────────────────────────────────────────────────
// Runtime error
// ─────────────────────────────────────────────────────────────────────────────

/// A runtime error raised by the VM.
#[derive(Debug, Clone)]
pub struct RuntimeError {
    pub message: String,
    pub stack_trace: Vec<String>,
}

impl std::fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)?;
        for frame in &self.stack_trace {
            write!(f, "\n  at {frame}")?;
        }
        Ok(())
    }
}

impl std::error::Error for RuntimeError {}

type VmResult<T> = Result<T, RuntimeError>;

// ─────────────────────────────────────────────────────────────────────────────
// CallFrame
// ─────────────────────────────────────────────────────────────────────────────

/// One active call on the call stack.
struct CallFrame {
    /// The closure (or module chunk wrapped in a synthetic closure) being executed.
    closure: ObjClosure,
    /// Current instruction pointer (index into `closure.proto.chunk.code`).
    ip: usize,
    /// Index in the VM's value stack where this frame's slot 0 lives.
    stack_base: usize,
}

impl CallFrame {
    fn chunk(&self) -> &Chunk {
        &self.closure.proto.chunk
    }

    fn read_byte(&mut self) -> u8 {
        let byte = self.chunk().code[self.ip];
        self.ip += 1;
        byte
    }

    fn read_u16(&mut self) -> u16 {
        let hi = self.chunk().code[self.ip] as u16;
        let lo = self.chunk().code[self.ip + 1] as u16;
        self.ip += 2;
        (hi << 8) | lo
    }

    fn current_line(&self) -> u32 {
        let ip = self.ip.saturating_sub(1);
        self.chunk().lines.get(ip).copied().unwrap_or(0)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Vm
// ─────────────────────────────────────────────────────────────────────────────

/// The Aura virtual machine.
pub struct Vm<'heap> {
    /// The garbage-collected heap (shared with the caller).
    heap: &'heap mut GcHeap,
    /// The value stack (shared across all call frames).
    stack: Vec<Value>,
    /// Active call frames (innermost last).
    frames: Vec<CallFrame>,
    /// Module-level global variable store.
    globals: HashMap<String, Value>,
    /// Source file path (for error messages and module resolution).
    #[allow(dead_code)]
    file_path: String,
    /// Registered native functions (index → function).
    natives: Vec<(String, NativeFn)>,
}

impl<'heap> Vm<'heap> {
    /// Create a new VM.  Call [`Vm::run`] to execute a module chunk.
    pub fn new(heap: &'heap mut GcHeap, file_path: &str) -> Self {
        let mut vm = Vm {
            heap,
            stack: Vec::with_capacity(256),
            frames: Vec::with_capacity(64),
            globals: HashMap::new(),
            file_path: file_path.to_string(),
            natives: Vec::new(),
        };
        crate::builtins::register_all(&mut vm);
        vm
    }

    /// Register a native function so it is available as a global.
    pub fn register_native(&mut self, name: &str, func: NativeFn) {
        let idx = self.natives.len();
        self.natives.push((name.to_string(), func));
        let val = Value::new_native(self.heap, name, func);
        self.globals.insert(name.to_string(), val);
        let _ = idx;
    }

    /// Execute the module-level [`Chunk`].
    ///
    /// The chunk is wrapped in a synthetic zero-argument closure and pushed as
    /// the first call frame.
    pub fn run(&mut self, chunk: Chunk) -> VmResult<()> {
        let proto = FnProto {
            name: "<module>".into(),
            arity: 0,
            chunk,
            upvalues: Vec::new(),
        };
        let closure = ObjClosure {
            proto,
            upvalues: Vec::new(),
        };
        self.frames.push(CallFrame {
            closure,
            ip: 0,
            stack_base: 0,
        });
        self.dispatch()
    }

    /// Execute a chunk as a library module (no main call).
    ///
    /// This runs the chunk's top-level code to register globals but does not
    /// look for or call a `main` function. Used for loading STL modules.
    pub fn run_module(&mut self, chunk: Chunk, name: &str) -> VmResult<()> {
        let proto = FnProto {
            name: name.into(),
            arity: 0,
            chunk,
            upvalues: Vec::new(),
        };
        let closure = ObjClosure {
            proto,
            upvalues: Vec::new(),
        };
        self.frames.push(CallFrame {
            closure,
            ip: 0,
            stack_base: 0,
        });
        self.dispatch()
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Main dispatch loop
    // ─────────────────────────────────────────────────────────────────────────

    fn dispatch(&mut self) -> VmResult<()> {
        loop {
            // Trigger GC if over threshold.
            if self.heap.should_collect() {
                let stack = &self.stack;
                let globals = &self.globals;
                self.heap.collect(|h| {
                    for v in stack.iter() {
                        crate::gc::GcTrace::trace(v, h);
                    }
                    for v in globals.values() {
                        crate::gc::GcTrace::trace(v, h);
                    }
                });
            }

            let frame = self.frames.last_mut().unwrap();
            let byte = frame.read_byte();
            let op = match OpCode::try_from(byte) {
                Ok(op) => op,
                Err(b) => return self.runtime_error(format!("unknown opcode: {b:#04x}")),
            };

            match op {
                // ── Constants ────────────────────────────────────────────────
                OpCode::Const => {
                    let idx = {
                        let frame = self.frames.last_mut().unwrap();
                        frame.read_u16() as usize
                    };
                    let val = self.constant_to_value(idx)?;
                    self.push(val);
                }
                OpCode::Int0 => self.push(Value::Int(0)),
                OpCode::Int1 => self.push(Value::Int(1)),
                OpCode::True => self.push(Value::Bool(true)),
                OpCode::False => self.push(Value::Bool(false)),
                OpCode::Null => self.push(Value::Null),

                // ── Stack ────────────────────────────────────────────────────
                OpCode::Pop => {
                    self.pop();
                }
                OpCode::Dup => {
                    let v = self.peek(0).clone();
                    self.push(v);
                }

                // ── Locals ───────────────────────────────────────────────────
                OpCode::LoadLocal => {
                    let (slot, base) = {
                        let frame = self.frames.last_mut().unwrap();
                        (frame.read_byte() as usize, frame.stack_base)
                    };
                    let val = self.stack[base + slot].clone();
                    self.push(val);
                }
                OpCode::StoreLocal => {
                    let (slot, base) = {
                        let frame = self.frames.last_mut().unwrap();
                        (frame.read_byte() as usize, frame.stack_base)
                    };
                    let val = self.peek(0).clone();
                    self.stack[base + slot] = val;
                }

                // ── Upvalues ─────────────────────────────────────────────────
                OpCode::LoadUpvalue => {
                    let idx = {
                        let frame = self.frames.last_mut().unwrap();
                        frame.read_byte() as usize
                    };
                    let val = {
                        let frame = self.frames.last().unwrap();
                        frame.closure.upvalues[idx].get(&self.stack).clone()
                    };
                    self.push(val);
                }
                OpCode::StoreUpvalue => {
                    let idx = {
                        let frame = self.frames.last_mut().unwrap();
                        frame.read_byte() as usize
                    };
                    let val = self.peek(0).clone();
                    let frame = self.frames.last_mut().unwrap();
                    frame.closure.upvalues[idx].set(&mut self.stack, val);
                }
                OpCode::CloseUpvalue => {
                    let (slot, base) = {
                        let frame = self.frames.last_mut().unwrap();
                        (frame.read_byte() as usize, frame.stack_base)
                    };
                    let absolute = base + slot;
                    // Close all upvalues that reference this slot.
                    for frame in self.frames.iter_mut() {
                        for uv in frame.closure.upvalues.iter_mut() {
                            if let Upvalue::Open(idx) = uv {
                                if *idx == absolute {
                                    uv.close(&self.stack);
                                }
                            }
                        }
                    }
                    self.stack.remove(absolute);
                }

                // ── Globals ──────────────────────────────────────────────────
                OpCode::LoadGlobal => {
                    let idx = {
                        let frame = self.frames.last_mut().unwrap();
                        frame.read_u16() as usize
                    };
                    let name = self.constant_as_str(idx)?;
                    let val = self.globals.get(&name).cloned().unwrap_or(Value::Null);
                    self.push(val);
                }
                OpCode::DefineGlobal => {
                    let idx = {
                        let frame = self.frames.last_mut().unwrap();
                        frame.read_u16() as usize
                    };
                    let name = self.constant_as_str(idx)?;
                    let val = self.pop();
                    self.globals.insert(name, val);
                }
                OpCode::StoreGlobal => {
                    let idx = {
                        let frame = self.frames.last_mut().unwrap();
                        frame.read_u16() as usize
                    };
                    let name = self.constant_as_str(idx)?;
                    let val = self.peek(0).clone();
                    self.globals.insert(name, val);
                }

                // ── Arithmetic ───────────────────────────────────────────────
                OpCode::Add => {
                    let b = self.pop();
                    let a = self.pop();
                    let result = match (&a, &b) {
                        (Value::Int(x), Value::Int(y)) => Value::Int(x.wrapping_add(*y)),
                        (Value::Float(x), Value::Float(y)) => Value::Float(x + y),
                        (Value::Int(x), Value::Float(y)) => Value::Float(*x as f64 + y),
                        (Value::Float(x), Value::Int(y)) => Value::Float(x + *y as f64),
                        (Value::Str(s1), Value::Str(s2)) => {
                            let s1 = unsafe { s1.as_ref().value.clone() };
                            let s2 = unsafe { s2.as_ref().value.clone() };
                            Value::new_str(self.heap, s1 + &s2)
                        }
                        _ => {
                            return self.runtime_error(format!(
                                "cannot add {} and {}",
                                a.type_name(),
                                b.type_name()
                            ))
                        }
                    };
                    self.push(result);
                }
                OpCode::Sub => {
                    let b = self.pop();
                    let a = self.pop();
                    let result = self.arith_op(&a, &b, |x, y| x - y, |x, y| x - y)?;
                    self.push(result);
                }
                OpCode::Mul => {
                    let b = self.pop();
                    let a = self.pop();
                    let result = self.arith_op(&a, &b, |x, y| x.wrapping_mul(y), |x, y| x * y)?;
                    self.push(result);
                }
                OpCode::Div => {
                    let b = self.pop();
                    let a = self.pop();
                    if matches!(b, Value::Int(0)) {
                        return self.runtime_error("division by zero");
                    }
                    let result = self.arith_op(&a, &b, |x, y| x / y, |x, y| x / y)?;
                    self.push(result);
                }
                OpCode::Rem => {
                    let b = self.pop();
                    let a = self.pop();
                    if matches!(b, Value::Int(0)) {
                        return self.runtime_error("remainder by zero");
                    }
                    let result = self.arith_op(&a, &b, |x, y| x % y, |x, y| x % y)?;
                    self.push(result);
                }
                OpCode::Neg => {
                    let a = self.pop();
                    let result = match a {
                        Value::Int(n) => Value::Int(-n),
                        Value::Float(f) => Value::Float(-f),
                        _ => return self.runtime_error(format!("cannot negate {}", a.type_name())),
                    };
                    self.push(result);
                }

                // ── Comparison ───────────────────────────────────────────────
                OpCode::CmpEq => {
                    let b = self.pop();
                    let a = self.pop();
                    self.push(Value::Bool(a == b));
                }
                OpCode::CmpNe => {
                    let b = self.pop();
                    let a = self.pop();
                    self.push(Value::Bool(a != b));
                }
                OpCode::CmpLt => {
                    let (a, b) = self.pop2();
                    self.push(self.cmp_op(a, b, |x, y| x < y, |x, y| x < y)?);
                }
                OpCode::CmpGt => {
                    let (a, b) = self.pop2();
                    self.push(self.cmp_op(a, b, |x, y| x > y, |x, y| x > y)?);
                }
                OpCode::CmpLe => {
                    let (a, b) = self.pop2();
                    self.push(self.cmp_op(a, b, |x, y| x <= y, |x, y| x <= y)?);
                }
                OpCode::CmpGe => {
                    let (a, b) = self.pop2();
                    self.push(self.cmp_op(a, b, |x, y| x >= y, |x, y| x >= y)?);
                }

                // ── Logic ────────────────────────────────────────────────────
                OpCode::Not => {
                    let a = self.pop();
                    self.push(Value::Bool(!a.is_truthy()));
                }
                OpCode::And => {
                    let target = {
                        let frame = self.frames.last_mut().unwrap();
                        frame.read_u16() as usize
                    };
                    // Top of stack is the LHS.  If falsy, jump (short-circuit).
                    if !self.peek(0).is_truthy() {
                        self.frames.last_mut().unwrap().ip = target;
                    }
                }
                OpCode::Or => {
                    let target = {
                        let frame = self.frames.last_mut().unwrap();
                        frame.read_u16() as usize
                    };
                    if self.peek(0).is_truthy() {
                        self.frames.last_mut().unwrap().ip = target;
                    }
                }

                // ── Jumps ────────────────────────────────────────────────────
                OpCode::Jump => {
                    let target = {
                        let frame = self.frames.last_mut().unwrap();
                        frame.read_u16() as usize
                    };
                    self.frames.last_mut().unwrap().ip = target;
                }
                OpCode::JumpIfFalse => {
                    let target = {
                        let frame = self.frames.last_mut().unwrap();
                        frame.read_u16() as usize
                    };
                    if !self.peek(0).is_truthy() {
                        self.frames.last_mut().unwrap().ip = target;
                    }
                }
                OpCode::JumpIfTrue => {
                    let target = {
                        let frame = self.frames.last_mut().unwrap();
                        frame.read_u16() as usize
                    };
                    if self.peek(0).is_truthy() {
                        self.frames.last_mut().unwrap().ip = target;
                    }
                }
                OpCode::JumpIfNull => {
                    let target = {
                        let frame = self.frames.last_mut().unwrap();
                        frame.read_u16() as usize
                    };
                    if self.peek(0).is_null() {
                        self.frames.last_mut().unwrap().ip = target;
                    }
                }
                OpCode::Loop => {
                    let target = {
                        let frame = self.frames.last_mut().unwrap();
                        frame.read_u16() as usize
                    };
                    self.frames.last_mut().unwrap().ip = target;
                }

                // ── Elvis ────────────────────────────────────────────────────
                OpCode::Elvis => {
                    let target = {
                        let frame = self.frames.last_mut().unwrap();
                        frame.read_u16() as usize
                    };
                    // If top is non-null, jump past RHS (keep top on stack).
                    if !self.peek(0).is_null() {
                        self.frames.last_mut().unwrap().ip = target;
                    }
                }

                // ── Calls ────────────────────────────────────────────────────
                OpCode::Call | OpCode::TailCall => {
                    let arg_count = {
                        let frame = self.frames.last_mut().unwrap();
                        frame.read_byte() as usize
                    };
                    self.call_value(arg_count)?;
                }
                OpCode::CallNative => {
                    // Native functions are registered as globals; CallNative is
                    // a direct index call for performance.
                    let idx = {
                        let frame = self.frames.last_mut().unwrap();
                        frame.read_byte() as usize
                    };
                    let arg_count = {
                        let frame = self.frames.last_mut().unwrap();
                        frame.read_byte() as usize
                    };
                    let func =
                        self.natives
                            .get(idx)
                            .map(|(_, f)| *f)
                            .ok_or_else(|| RuntimeError {
                                message: format!("native index {idx} out of range"),
                                stack_trace: Vec::new(),
                            })?;
                    let base = self.stack.len() - arg_count;
                    let args: Vec<Value> = self.stack.drain(base..).collect();
                    let result = func(&args).map_err(|e| RuntimeError {
                        message: e,
                        stack_trace: Vec::new(),
                    })?;
                    self.push(result);
                }
                OpCode::CallMethod => {
                    let (method_name_idx, arg_count) = {
                        let frame = self.frames.last_mut().unwrap();
                        let idx = frame.read_u16() as usize;
                        let count = frame.read_byte() as usize;
                        (idx, count)
                    };
                    let method_name = self.constant_as_str(method_name_idx)?;
                    let receiver_idx = self.stack.len() - 1 - arg_count;
                    let receiver = self.stack[receiver_idx].clone();
                    // For structs, use the internal type_name field for method dispatch.
                    // This allows deftype File(fd) instances to resolve File.method().
                    let type_name = match &receiver {
                        Value::Struct(s) => {
                            let s = unsafe { s.as_ref() };
                            if s.type_name.is_empty() {
                                "Struct"
                            } else {
                                &s.type_name
                            }
                        }
                        _ => receiver.type_name(),
                    };
                    let full_name = format!("{}.{}", type_name, method_name);

                    let callee =
                        self.globals
                            .get(&full_name)
                            .cloned()
                            .ok_or_else(|| RuntimeError {
                                message: format!(
                                    "no method `{}` on type {}",
                                    method_name, type_name
                                ),
                                stack_trace: Vec::new(),
                            })?;

                    // Insert callee before receiver: stack becomes [..., callee, receiver, args...]
                    // Then call with arg_count + 1 (receiver is first arg)
                    self.stack.insert(receiver_idx, callee);
                    self.call_value(arg_count + 1)?;
                }
                OpCode::Return => {
                    let return_val = self.pop();
                    let frame = self.frames.pop().unwrap();
                    if self.frames.is_empty() {
                        // Module frame finished.
                        return Ok(());
                    }
                    // Truncate the stack to where the callee started.
                    self.stack.truncate(frame.stack_base);
                    // Pop the callee (it was below stack_base).
                    if !self.stack.is_empty() {
                        self.stack.pop();
                    }
                    self.push(return_val);
                }

                // ── Closures ─────────────────────────────────────────────────
                OpCode::Closure => {
                    let idx = {
                        let frame = self.frames.last_mut().unwrap();
                        frame.read_u16() as usize
                    };
                    let proto = self.get_fn_proto(idx)?;
                    let upvalue_descs = proto.upvalues.clone();
                    let mut upvalues: Vec<Upvalue> = Vec::new();
                    for desc in &upvalue_descs {
                        let uv = if desc.is_local {
                            let base = self.frames.last().unwrap().stack_base;
                            Upvalue::Open(base + desc.index as usize)
                        } else {
                            // Capture from enclosing closure's upvalues.
                            let enc_uv =
                                &self.frames.last().unwrap().closure.upvalues[desc.index as usize];
                            enc_uv.clone()
                        };
                        upvalues.push(uv);
                    }
                    let val = Value::new_closure(self.heap, proto, upvalues);
                    self.push(val);
                }

                // ── Collections ──────────────────────────────────────────────
                OpCode::MakeList => {
                    let count = {
                        let frame = self.frames.last_mut().unwrap();
                        frame.read_u16() as usize
                    };
                    let base = self.stack.len() - count;
                    let items: Vec<Value> = self.stack.drain(base..).collect();
                    let val = Value::new_list(self.heap, items);
                    self.push(val);
                }
                OpCode::MakeDict => {
                    let count = {
                        let frame = self.frames.last_mut().unwrap();
                        frame.read_u16() as usize
                    };
                    let base = self.stack.len() - count * 2;
                    let pairs: Vec<Value> = self.stack.drain(base..).collect();
                    let mut map = std::collections::HashMap::new();
                    for chunk in pairs.chunks(2) {
                        let key = match &chunk[0] {
                            // SAFETY: string is alive (just from the stack).
                            Value::Str(s) => unsafe { s.as_ref().value.clone() },
                            other => format!("{other}"),
                        };
                        map.insert(key, chunk[1].clone());
                    }
                    let val = Value::new_dict(self.heap, map);
                    self.push(val);
                }
                OpCode::MakeTuple => {
                    let count = {
                        let frame = self.frames.last_mut().unwrap();
                        frame.read_u16() as usize
                    };
                    let base = self.stack.len() - count;
                    let items: Vec<Value> = self.stack.drain(base..).collect();
                    let val = Value::new_tuple(self.heap, items);
                    self.push(val);
                }
                OpCode::MakeStruct => {
                    let field_count = {
                        let frame = self.frames.last_mut().unwrap();
                        frame.read_u16() as usize
                    };
                    let base = self.stack.len() - field_count * 2;
                    let pairs: Vec<Value> = self.stack.drain(base..).collect();
                    let mut fields: Vec<(String, Value)> = Vec::new();
                    for chunk in pairs.chunks(2) {
                        let name = match &chunk[0] {
                            // SAFETY: string is alive (just from the stack).
                            Value::Str(s) => unsafe { s.as_ref().value.clone() },
                            other => format!("{other}"),
                        };
                        fields.push((name, chunk[1].clone()));
                    }
                    let val = Value::new_struct(self.heap, "", fields);
                    self.push(val);
                }
                OpCode::MakeTypedStruct => {
                    let (type_name_idx, field_count) = {
                        let frame = self.frames.last_mut().unwrap();
                        let type_idx = frame.read_u16() as usize;
                        let count = frame.read_u16() as usize;
                        (type_idx, count)
                    };
                    let type_name = self.constant_as_str(type_name_idx)?.to_string();
                    let base = self.stack.len() - field_count * 2;
                    let pairs: Vec<Value> = self.stack.drain(base..).collect();
                    let mut fields: Vec<(String, Value)> = Vec::new();
                    for chunk in pairs.chunks(2) {
                        let name = match &chunk[0] {
                            Value::Str(s) => unsafe { s.as_ref().value.clone() },
                            other => format!("{other}"),
                        };
                        fields.push((name, chunk[1].clone()));
                    }
                    let val = Value::new_struct(self.heap, type_name, fields);
                    self.push(val);
                }

                // ── Field / index ────────────────────────────────────────────
                OpCode::GetField => {
                    let idx = {
                        let frame = self.frames.last_mut().unwrap();
                        frame.read_u16() as usize
                    };
                    let name = self.constant_as_str(idx)?;
                    let obj = self.pop();
                    let val = self.get_field(obj, &name)?;
                    self.push(val);
                }
                OpCode::SetField => {
                    let idx = {
                        let frame = self.frames.last_mut().unwrap();
                        frame.read_u16() as usize
                    };
                    let name = self.constant_as_str(idx)?;
                    let value = self.pop();
                    let obj = self.peek(0).clone();
                    self.set_field(obj, &name, value)?;
                }
                OpCode::GetIndex => {
                    let index = self.pop();
                    let obj = self.pop();
                    let val = self.get_index(obj, index)?;
                    self.push(val);
                }
                OpCode::SetIndex => {
                    let value = self.pop();
                    let index = self.pop();
                    let obj = self.peek(0).clone();
                    self.set_index(obj, index, value)?;
                }

                // ── String concatenation ─────────────────────────────────────
                OpCode::StrConcat => {
                    let count = {
                        let frame = self.frames.last_mut().unwrap();
                        frame.read_u16() as usize
                    };
                    let base = self.stack.len() - count;
                    let parts: Vec<Value> = self.stack.drain(base..).collect();
                    let mut buf = String::new();
                    for part in &parts {
                        buf.push_str(&format!("{part}"));
                    }
                    let val = Value::new_str(self.heap, buf);
                    self.push(val);
                }

                // ── Misc ─────────────────────────────────────────────────────
                OpCode::ToBool => {
                    let v = self.pop();
                    self.push(Value::Bool(v.is_truthy()));
                }
                OpCode::ForceUnwrap => {
                    let v = self.pop();
                    if v.is_null() {
                        return self.runtime_error("force-unwrap on null value");
                    }
                    // Unwrap Option/Result variant structs: `.some(x)` / `.ok(x)` → `x`.
                    // `.null` / `.error(msg)` / `.none` are treated as failure.
                    if let Value::Str(s_ptr) = &v {
                        let tag = unsafe { s_ptr.as_ref() }.value.clone();
                        if tag == ".null" || tag == ".none" || tag == ".error" {
                            return self
                                .runtime_error(format!("force-unwrap on failure variant `{tag}`"));
                        }
                        self.push(v);
                    } else if let Value::Struct(s_ptr) = &v {
                        let s = unsafe { s_ptr.as_ref() };
                        match s.type_name.as_str() {
                            "some" | "ok" => {
                                // Extract the inner `value` field.
                                let inner = s.get_field("value").cloned().unwrap_or(Value::Null);
                                self.push(inner);
                            }
                            "null" | "none" | "error" => {
                                let tag = s.type_name.clone();
                                return self.runtime_error(format!(
                                    "force-unwrap on failure variant `.{tag}`"
                                ));
                            }
                            _ => {
                                // Unknown struct variant — pass through unchanged.
                                self.push(v);
                            }
                        }
                    } else {
                        self.push(v);
                    }
                }
                OpCode::GetTag => {
                    let v = self.pop();
                    let tag = match &v {
                        Value::Struct(s) => unsafe { s.as_ref() }.type_name.clone(),
                        _ => String::new(),
                    };
                    let tag_val = Value::new_str(self.heap, tag);
                    self.push(tag_val);
                }
                OpCode::PostInc => {
                    let (slot, base) = {
                        let frame = self.frames.last_mut().unwrap();
                        (frame.read_byte() as usize, frame.stack_base)
                    };
                    let old = self.stack[base + slot].clone();
                    let new_val = match &old {
                        Value::Int(n) => Value::Int(n + 1),
                        Value::Float(f) => Value::Float(f + 1.0),
                        _ => return self.runtime_error("++ on non-numeric value"),
                    };
                    self.stack[base + slot] = new_val;
                    self.push(old);
                }
                OpCode::PostDec => {
                    let (slot, base) = {
                        let frame = self.frames.last_mut().unwrap();
                        (frame.read_byte() as usize, frame.stack_base)
                    };
                    let old = self.stack[base + slot].clone();
                    let new_val = match &old {
                        Value::Int(n) => Value::Int(n - 1),
                        Value::Float(f) => Value::Float(f - 1.0),
                        _ => return self.runtime_error("-- on non-numeric value"),
                    };
                    self.stack[base + slot] = new_val;
                    self.push(old);
                }
                OpCode::Nop => {}
            }
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Call dispatch
    // ─────────────────────────────────────────────────────────────────────────

    fn call_value(&mut self, arg_count: usize) -> VmResult<()> {
        let callee_idx = self.stack.len() - 1 - arg_count;
        let callee = self.stack[callee_idx].clone();

        match callee {
            Value::Closure(closure_ptr) => {
                // SAFETY: the closure is live (it's on the stack).
                let closure = unsafe { closure_ptr.as_ref() };
                if closure.proto.arity as usize != arg_count {
                    return self.runtime_error(format!(
                        "function `{}` expects {} arguments, got {}",
                        closure.proto.name, closure.proto.arity, arg_count
                    ));
                }
                let stack_base = callee_idx + 1;
                let new_closure = closure.clone(); // Clone to avoid borrow conflict.
                self.frames.push(CallFrame {
                    closure: new_closure,
                    ip: 0,
                    stack_base,
                });
                Ok(())
            }
            Value::Native(native_ptr) => {
                // SAFETY: native is live.
                let native = unsafe { native_ptr.as_ref() };
                let func = native.func;
                let base = self.stack.len() - arg_count;
                let args: Vec<Value> = self.stack.drain(base..).collect();
                // Pop the callee too.
                self.stack.pop();
                let result = func(&args).map_err(|e| RuntimeError {
                    message: e,
                    stack_trace: Vec::new(),
                })?;
                self.push(result);
                Ok(())
            }
            // ── Variant constructor: calling `.ok`, `.some`, `.error`, etc. ──
            // A dot-ident string (e.g. `".ok"`) followed by arguments is
            // treated as a variant constructor.  With one argument it produces
            // `Struct { type_name: "ok", fields: [("value", arg)] }`.  With
            // zero arguments it is a no-op (the bare string is the variant,
            // e.g. `.null` stays as `Value::Str(".null")`).
            Value::Str(s_ptr) => {
                let tag = unsafe { s_ptr.as_ref() }.value.clone();
                if let Some(variant_name) = tag.strip_prefix('.') {
                    let variant_name = variant_name.to_string();
                    let base = self.stack.len() - arg_count;
                    let args: Vec<Value> = self.stack.drain(base..).collect();
                    // Pop the callee string.
                    self.stack.pop();
                    let result = match arg_count {
                        0 => {
                            // Zero-arg variant: just re-push the dot-ident string.
                            Value::new_str(self.heap, tag)
                        }
                        1 => Value::new_struct(
                            self.heap,
                            variant_name,
                            vec![("value".to_string(), args.into_iter().next().unwrap())],
                        ),
                        _ => {
                            // Multi-arg variant: fields named "0", "1", ...
                            let fields: Vec<(String, Value)> = args
                                .into_iter()
                                .enumerate()
                                .map(|(i, v)| (i.to_string(), v))
                                .collect();
                            Value::new_struct(self.heap, variant_name, fields)
                        }
                    };
                    self.push(result);
                    Ok(())
                } else {
                    self.runtime_error("cannot call value of type String".to_string())
                }
            }
            other => self.runtime_error(format!("cannot call value of type {}", other.type_name())),
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Field / index operations
    // ─────────────────────────────────────────────────────────────────────────

    fn get_field(&self, obj: Value, name: &str) -> VmResult<Value> {
        match &obj {
            Value::Struct(s) => {
                let s = unsafe { s.as_ref() };
                Ok(s.get_field(name).cloned().unwrap_or(Value::Null))
            }
            Value::Module(m) => {
                let m = unsafe { m.as_ref() };
                Ok(m.exports.get(name).cloned().unwrap_or(Value::Null))
            }
            _ => Err(RuntimeError {
                message: format!("cannot access field `{name}` on {}", obj.type_name()),
                stack_trace: Vec::new(),
            }),
        }
    }

    fn set_field(&self, obj: Value, name: &str, val: Value) -> VmResult<()> {
        match &obj {
            Value::Struct(s) => {
                let s = unsafe { s.as_mut() };
                if !s.set_field(name, val) {
                    return Err(RuntimeError {
                        message: format!("no field `{name}` on struct"),
                        stack_trace: Vec::new(),
                    });
                }
                Ok(())
            }
            _ => Err(RuntimeError {
                message: format!("cannot set field `{name}` on {}", obj.type_name()),
                stack_trace: Vec::new(),
            }),
        }
    }

    fn get_index(&self, obj: Value, index: Value) -> VmResult<Value> {
        match (&obj, &index) {
            (Value::List(l), Value::Int(i)) => {
                let list = unsafe { l.as_ref() };
                let items = list.items.borrow();
                let idx = if *i < 0 { items.len() as i64 + i } else { *i } as usize;
                Ok(items.get(idx).cloned().unwrap_or(Value::Null))
            }
            (Value::Dict(d), _) => {
                let dict = unsafe { d.as_ref() };
                let key = format!("{index}");
                Ok(dict.map.borrow().get(&key).cloned().unwrap_or(Value::Null))
            }
            (Value::Tuple(t), Value::Int(i)) => {
                let tup = unsafe { t.as_ref() };
                let idx = if *i < 0 {
                    tup.items.len() as i64 + i
                } else {
                    *i
                } as usize;
                Ok(tup.items.get(idx).cloned().unwrap_or(Value::Null))
            }
            _ => Err(RuntimeError {
                message: format!(
                    "cannot index {} with {}",
                    obj.type_name(),
                    index.type_name()
                ),
                stack_trace: Vec::new(),
            }),
        }
    }

    fn set_index(&self, obj: Value, index: Value, val: Value) -> VmResult<()> {
        match (&obj, &index) {
            (Value::List(l), Value::Int(i)) => {
                let list = unsafe { l.as_ref() };
                let mut items = list.items.borrow_mut();
                let idx = if *i < 0 { items.len() as i64 + i } else { *i } as usize;
                if idx < items.len() {
                    items[idx] = val;
                } else {
                    return Err(RuntimeError {
                        message: format!("list index {idx} out of bounds"),
                        stack_trace: Vec::new(),
                    });
                }
                Ok(())
            }
            (Value::Dict(d), _) => {
                let dict = unsafe { d.as_ref() };
                let key = format!("{index}");
                dict.map.borrow_mut().insert(key, val);
                Ok(())
            }
            _ => Err(RuntimeError {
                message: format!("cannot set index on {}", obj.type_name()),
                stack_trace: Vec::new(),
            }),
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Constant pool helpers
    // ─────────────────────────────────────────────────────────────────────────

    fn constant_to_value(&mut self, idx: usize) -> VmResult<Value> {
        let constant = {
            let frame = self.frames.last().unwrap();
            frame.chunk().constants.get(idx).cloned()
        };
        match constant {
            Some(Constant::Int(n)) => Ok(Value::Int(n)),
            Some(Constant::Float(f)) => Ok(Value::Float(f)),
            Some(Constant::Bool(b)) => Ok(Value::Bool(b)),
            Some(Constant::Null) => Ok(Value::Null),
            Some(Constant::Str(s)) => Ok(Value::new_str(self.heap, s)),
            Some(Constant::FnProto(p)) => {
                // Produce a bare Closure with no upvalues (upvalues are captured by OpCode::Closure).
                Ok(Value::new_closure(self.heap, *p, Vec::new()))
            }
            None => self.runtime_error(format!("constant index {idx} out of range")),
        }
    }

    fn constant_as_str(&self, idx: usize) -> VmResult<String> {
        let frame = self.frames.last().unwrap();
        match frame.chunk().constants.get(idx) {
            Some(Constant::Str(s)) => Ok(s.clone()),
            other => Err(RuntimeError {
                message: format!("expected string constant at {idx}, got {other:?}"),
                stack_trace: Vec::new(),
            }),
        }
    }

    fn get_fn_proto(&self, idx: usize) -> VmResult<FnProto> {
        let frame = self.frames.last().unwrap();
        match frame.chunk().constants.get(idx) {
            Some(Constant::FnProto(p)) => Ok(*p.clone()),
            other => Err(RuntimeError {
                message: format!("expected FnProto at {idx}, got {other:?}"),
                stack_trace: Vec::new(),
            }),
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Stack helpers
    // ─────────────────────────────────────────────────────────────────────────

    #[inline]
    fn push(&mut self, val: Value) {
        self.stack.push(val);
    }

    #[inline]
    fn pop(&mut self) -> Value {
        self.stack.pop().expect("stack underflow")
    }

    #[inline]
    fn pop2(&mut self) -> (Value, Value) {
        let b = self.pop();
        let a = self.pop();
        (a, b)
    }

    #[inline]
    fn peek(&self, distance: usize) -> &Value {
        let idx = self.stack.len() - 1 - distance;
        &self.stack[idx]
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Arithmetic helpers
    // ─────────────────────────────────────────────────────────────────────────

    fn arith_op(
        &self,
        a: &Value,
        b: &Value,
        int_op: impl Fn(i64, i64) -> i64,
        float_op: impl Fn(f64, f64) -> f64,
    ) -> VmResult<Value> {
        match (a, b) {
            (Value::Int(x), Value::Int(y)) => Ok(Value::Int(int_op(*x, *y))),
            (Value::Float(x), Value::Float(y)) => Ok(Value::Float(float_op(*x, *y))),
            (Value::Int(x), Value::Float(y)) => Ok(Value::Float(float_op(*x as f64, *y))),
            (Value::Float(x), Value::Int(y)) => Ok(Value::Float(float_op(*x, *y as f64))),
            _ => Err(RuntimeError {
                message: format!(
                    "arithmetic requires numeric operands, got {} and {}",
                    a.type_name(),
                    b.type_name()
                ),
                stack_trace: Vec::new(),
            }),
        }
    }

    fn cmp_op(
        &self,
        a: Value,
        b: Value,
        int_cmp: impl Fn(i64, i64) -> bool,
        float_cmp: impl Fn(f64, f64) -> bool,
    ) -> VmResult<Value> {
        let result = match (&a, &b) {
            (Value::Int(x), Value::Int(y)) => int_cmp(*x, *y),
            (Value::Float(x), Value::Float(y)) => float_cmp(*x, *y),
            (Value::Int(x), Value::Float(y)) => float_cmp(*x as f64, *y),
            (Value::Float(x), Value::Int(y)) => float_cmp(*x, *y as f64),
            _ => {
                return Err(RuntimeError {
                    message: format!(
                        "comparison requires numeric operands, got {} and {}",
                        a.type_name(),
                        b.type_name()
                    ),
                    stack_trace: Vec::new(),
                })
            }
        };
        Ok(Value::Bool(result))
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Error helpers
    // ─────────────────────────────────────────────────────────────────────────

    fn runtime_error<T>(&self, msg: impl Into<String>) -> VmResult<T> {
        let stack_trace: Vec<String> = self
            .frames
            .iter()
            .rev()
            .map(|f| format!("{}:{}", f.closure.proto.name, f.current_line()))
            .collect();
        Err(RuntimeError {
            message: msg.into(),
            stack_trace,
        })
    }
}
