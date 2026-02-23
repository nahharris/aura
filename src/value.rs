//! Runtime values for the Aura VM.
//!
//! The [`Value`] enum is the central representation of all data at runtime.
//! Scalar values (`Int`, `Float`, `Bool`, `Null`) are stored inline.
//! Heap-allocated objects (`Str`, `List`, `Dict`, `Closure`, etc.) are
//! accessed through a [`GcPtr`] so the garbage collector can track them.
//!
//! # Object variants
//!
//! | Variant | Heap type | Notes |
//! |---------|-----------|-------|
//! | `Value::Str(GcPtr<ObjString>)` | `ObjString` | Immutable UTF-8 string |
//! | `Value::List(GcPtr<ObjList>)` | `ObjList` | Growable `Vec<Value>` |
//! | `Value::Dict(GcPtr<ObjDict>)` | `ObjDict` | `HashMap<String, Value>` |
//! | `Value::Tuple(GcPtr<ObjTuple>)` | `ObjTuple` | Fixed-length `Vec<Value>` |
//! | `Value::Struct(GcPtr<ObjStruct>)` | `ObjStruct` | Named fields (`HashMap`) |
//! | `Value::Closure(GcPtr<ObjClosure>)` | `ObjClosure` | Function proto + upvalues |
//! | `Value::Native(GcPtr<ObjNative>)` | `ObjNative` | Rust native function |
//! | `Value::Module(GcPtr<ObjModule>)` | `ObjModule` | Loaded module namespace |

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;

use crate::bytecode::FnProto;
use crate::gc::{GcHeap, GcPtr, GcTrace};

// ─────────────────────────────────────────────────────────────────────────────
// Value
// ─────────────────────────────────────────────────────────────────────────────

/// A runtime value in the Aura VM.
#[derive(Clone, Debug)]
pub enum Value {
    /// 64-bit signed integer.
    Int(i64),
    /// 64-bit IEEE-754 float.
    Float(f64),
    /// Boolean.
    Bool(bool),
    /// A Unicode character.
    Char(char),
    /// The null value.
    Null,
    /// A heap-allocated string.
    Str(GcPtr<ObjString>),
    /// A heap-allocated list (`Vec<Value>`).
    List(GcPtr<ObjList>),
    /// A heap-allocated dictionary (`HashMap<String, Value>`).
    Dict(GcPtr<ObjDict>),
    /// A heap-allocated fixed-length tuple.
    Tuple(GcPtr<ObjTuple>),
    /// A heap-allocated named-field struct.
    Struct(GcPtr<ObjStruct>),
    /// A heap-allocated closure (function prototype + captured upvalues).
    Closure(GcPtr<ObjClosure>),
    /// A native (Rust) function.
    Native(GcPtr<ObjNative>),
    /// A loaded module namespace.
    Module(GcPtr<ObjModule>),
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Float(a), Value::Float(b)) => a == b,
            (Value::Int(a), Value::Float(b)) => (*a as f64) == *b,
            (Value::Float(a), Value::Int(b)) => *a == (*b as f64),
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Char(a), Value::Char(b)) => a == b,
            (Value::Null, Value::Null) => true,
            (Value::Str(a), Value::Str(b)) => {
                // SAFETY: strings are alive as long as they're on the stack.
                let a = unsafe { a.as_ref() };
                let b = unsafe { b.as_ref() };
                a.value == b.value
            }
            (Value::List(a), Value::List(b)) => a == b,
            (Value::Tuple(a), Value::Tuple(b)) => a == b,
            (Value::Closure(a), Value::Closure(b)) => a == b,
            (Value::Native(a), Value::Native(b)) => a == b,
            _ => false,
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Int(n) => write!(f, "{n}"),
            Value::Float(n) => {
                // Print integers without a decimal point if possible.
                if n.fract() == 0.0 && n.is_finite() {
                    write!(f, "{n:.1}")
                } else {
                    write!(f, "{n}")
                }
            }
            Value::Bool(b) => write!(f, "{b}"),
            Value::Char(c) => write!(f, "{c}"),
            Value::Null => write!(f, "null"),
            Value::Str(s) => {
                // SAFETY: value is alive (on the stack or in a live object).
                let s = unsafe { s.as_ref() };
                write!(f, "{}", s.value)
            }
            Value::List(l) => {
                let l = unsafe { l.as_ref() };
                write!(f, "[")?;
                for (i, v) in l.items.borrow().iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{v}")?;
                }
                write!(f, "]")
            }
            Value::Dict(d) => {
                let d = unsafe { d.as_ref() };
                write!(f, "{{")?;
                for (i, (k, v)) in d.map.borrow().iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{k:?}: {v}")?;
                }
                write!(f, "}}")
            }
            Value::Tuple(t) => {
                let t = unsafe { t.as_ref() };
                write!(f, "(")?;
                for (i, v) in t.items.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{v}")?;
                }
                write!(f, ")")
            }
            Value::Struct(s) => {
                let s = unsafe { s.as_ref() };
                if s.type_name.is_empty() {
                    write!(f, "(")?;
                } else {
                    write!(f, ".{}(", s.type_name)?;
                }
                for (i, (k, v)) in s.fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    // For single-field variants produced by dot-ident constructors
                    // the field is named "value"; omit the key for cleaner display.
                    if k == "value" && s.fields.len() == 1 {
                        write!(f, "{v}")?;
                    } else {
                        write!(f, "{k} = {v}")?;
                    }
                }
                write!(f, ")")
            }
            Value::Closure(c) => {
                let c = unsafe { c.as_ref() };
                write!(f, "<fn {}>", c.proto.name)
            }
            Value::Native(n) => {
                let n = unsafe { n.as_ref() };
                write!(f, "<native {}>", n.name)
            }
            Value::Module(m) => {
                let m = unsafe { m.as_ref() };
                write!(f, "<module {}>", m.name)
            }
        }
    }
}

impl Value {
    /// Return `true` if this value is truthy (non-null, non-false, non-zero).
    pub fn is_truthy(&self) -> bool {
        match self {
            Value::Null => false,
            Value::Bool(b) => *b,
            Value::Int(n) => *n != 0,
            Value::Float(n) => *n != 0.0,
            Value::Char(c) => *c != '\0',
            _ => true,
        }
    }

    /// Return `true` if this value is `null`.
    #[inline]
    pub fn is_null(&self) -> bool {
        matches!(self, Value::Null)
    }

    /// Return a human-readable type name for error messages.
    pub fn type_name(&self) -> &'static str {
        match self {
            Value::Int(_) => "Int",
            Value::Float(_) => "Float",
            Value::Bool(_) => "Bool",
            Value::Char(_) => "Char",
            Value::Null => "Null",
            Value::Str(_) => "String",
            Value::List(_) => "List",
            Value::Dict(_) => "Dict",
            Value::Tuple(_) => "Tuple",
            Value::Struct(_) => "Struct",
            Value::Closure(_) => "Closure",
            Value::Native(_) => "Native",
            Value::Module(_) => "Module",
        }
    }

    /// Try to get the integer value, returning `None` if not an integer.
    pub fn as_int(&self) -> Option<i64> {
        match self {
            Value::Int(n) => Some(*n),
            _ => None,
        }
    }

    /// Try to get a float (also accepts int by widening).
    pub fn as_float(&self) -> Option<f64> {
        match self {
            Value::Float(f) => Some(*f),
            Value::Int(n) => Some(*n as f64),
            _ => None,
        }
    }

    /// Try to get the string content.
    ///
    /// # Safety
    /// The string object must be alive (not collected).
    pub unsafe fn as_str(&self) -> Option<&str> {
        match self {
            // SAFETY: caller guarantees liveness.
            Value::Str(s) => Some(unsafe { &s.as_ref().value }),
            _ => None,
        }
    }
}

// GcTrace implementation for Value — routes into the heap for all pointer variants.
impl GcTrace for Value {
    fn trace(&self, heap: &mut GcHeap) {
        match self {
            Value::Str(p) => heap.mark(p.as_dyn_trace()),
            Value::List(p) => heap.mark(p.as_dyn_trace()),
            Value::Dict(p) => heap.mark(p.as_dyn_trace()),
            Value::Tuple(p) => heap.mark(p.as_dyn_trace()),
            Value::Struct(p) => heap.mark(p.as_dyn_trace()),
            Value::Closure(p) => heap.mark(p.as_dyn_trace()),
            Value::Native(p) => heap.mark(p.as_dyn_trace()),
            Value::Module(p) => heap.mark(p.as_dyn_trace()),
            // Scalars have no heap children.
            Value::Int(_) | Value::Float(_) | Value::Bool(_) | Value::Char(_) | Value::Null => {}
        }
    }

    fn heap_size(&self) -> usize {
        0
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Helper trait so GcPtr<T: GcTrace + Sized> can produce GcPtr<dyn GcTrace>
// ─────────────────────────────────────────────────────────────────────────────

/// Extension trait: convert a typed `GcPtr<T>` to an erased `GcPtr<dyn GcTrace>`.
pub trait AsDynTrace {
    #[allow(clippy::wrong_self_convention)]
    fn as_dyn_trace(self) -> GcPtr<dyn GcTrace>;
}

impl<T: GcTrace + Sized + 'static> AsDynTrace for GcPtr<T> {
    fn as_dyn_trace(self) -> GcPtr<dyn GcTrace> {
        self.as_dyn()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Heap object types
// ─────────────────────────────────────────────────────────────────────────────

// ── ObjString ────────────────────────────────────────────────────────────────

/// A heap-allocated UTF-8 string.
#[derive(Debug)]
pub struct ObjString {
    pub value: String,
}

impl GcTrace for ObjString {
    fn trace(&self, _heap: &mut GcHeap) {}
    fn heap_size(&self) -> usize {
        self.value.capacity()
    }
}

// ── ObjList ───────────────────────────────────────────────────────────────────

/// A heap-allocated growable list.
#[derive(Debug)]
pub struct ObjList {
    pub items: RefCell<Vec<Value>>,
}

impl GcTrace for ObjList {
    fn trace(&self, heap: &mut GcHeap) {
        for v in self.items.borrow().iter() {
            v.trace(heap);
        }
    }
    fn heap_size(&self) -> usize {
        self.items.borrow().capacity() * std::mem::size_of::<Value>()
    }
}

// ── ObjDict ───────────────────────────────────────────────────────────────────

/// A heap-allocated dictionary with string keys.
#[derive(Debug)]
pub struct ObjDict {
    pub map: RefCell<HashMap<String, Value>>,
}

impl GcTrace for ObjDict {
    fn trace(&self, heap: &mut GcHeap) {
        for v in self.map.borrow().values() {
            v.trace(heap);
        }
    }
    fn heap_size(&self) -> usize {
        self.map.borrow().capacity()
            * (std::mem::size_of::<String>() + std::mem::size_of::<Value>())
    }
}

// ── ObjTuple ─────────────────────────────────────────────────────────────────

/// A heap-allocated fixed-length positional tuple.
#[derive(Debug)]
pub struct ObjTuple {
    pub items: Vec<Value>,
}

impl GcTrace for ObjTuple {
    fn trace(&self, heap: &mut GcHeap) {
        for v in &self.items {
            v.trace(heap);
        }
    }
    fn heap_size(&self) -> usize {
        self.items.capacity() * std::mem::size_of::<Value>()
    }
}

// ── ObjStruct ────────────────────────────────────────────────────────────────

/// A heap-allocated named-field struct value.
///
/// Fields are stored in insertion order for deterministic `Display` output.
#[derive(Debug)]
pub struct ObjStruct {
    /// Type name (e.g., `"Point"`), or empty string for anonymous structs.
    pub type_name: String,
    /// Fields in declaration order: `(name, value)` pairs.
    pub fields: Vec<(String, Value)>,
}

impl ObjStruct {
    /// Look up a field by name.
    pub fn get_field(&self, name: &str) -> Option<&Value> {
        self.fields.iter().find(|(k, _)| k == name).map(|(_, v)| v)
    }

    /// Set a field (mutable borrow).
    pub fn set_field(&mut self, name: &str, val: Value) -> bool {
        if let Some((_, v)) = self.fields.iter_mut().find(|(k, _)| k == name) {
            *v = val;
            true
        } else {
            false
        }
    }
}

impl GcTrace for ObjStruct {
    fn trace(&self, heap: &mut GcHeap) {
        for (_, v) in &self.fields {
            v.trace(heap);
        }
    }
    fn heap_size(&self) -> usize {
        self.fields.capacity() * (std::mem::size_of::<String>() + std::mem::size_of::<Value>())
    }
}

// ── ObjClosure ────────────────────────────────────────────────────────────────

/// A heap-allocated closure: a function prototype plus its captured upvalues.
#[derive(Debug, Clone)]
pub struct ObjClosure {
    /// The compiled function prototype.
    pub proto: FnProto,
    /// The captured upvalues (one per `proto.upvalues` descriptor).
    pub upvalues: Vec<Upvalue>,
}

impl GcTrace for ObjClosure {
    fn trace(&self, heap: &mut GcHeap) {
        for uv in &self.upvalues {
            uv.trace(heap);
        }
    }
    fn heap_size(&self) -> usize {
        self.upvalues.capacity() * std::mem::size_of::<Upvalue>()
    }
}

// ── Upvalue ────────────────────────────────────────────────────────────────────

/// A captured variable: either still on the stack (open) or moved to the heap
/// (closed).
///
/// An upvalue starts **open**: it holds a stack-slot index into the enclosing
/// call frame.  When the enclosing frame exits, `CloseUpvalue` moves the live
/// value onto the heap (the upvalue becomes **closed**).
#[derive(Debug, Clone)]
pub enum Upvalue {
    /// Still on the stack.  The `usize` is the stack index of the live local.
    Open(usize),
    /// Moved off the stack onto the heap.
    Closed(Box<Value>),
}

impl Upvalue {
    /// Get the current value, given the VM stack (used for open upvalues).
    pub fn get<'a>(&'a self, stack: &'a [Value]) -> &'a Value {
        match self {
            Upvalue::Open(idx) => &stack[*idx],
            Upvalue::Closed(v) => v,
        }
    }

    /// Set the value.
    pub fn set(&mut self, stack: &mut [Value], val: Value) {
        match self {
            Upvalue::Open(idx) => stack[*idx] = val,
            Upvalue::Closed(v) => **v = val,
        }
    }

    /// Close this upvalue: copy the current value off the stack.
    pub fn close(&mut self, stack: &[Value]) {
        if let Upvalue::Open(idx) = self {
            let val = stack[*idx].clone();
            *self = Upvalue::Closed(Box::new(val));
        }
    }
}

impl GcTrace for Upvalue {
    fn trace(&self, heap: &mut GcHeap) {
        if let Upvalue::Closed(v) = self {
            v.trace(heap);
        }
    }
    fn heap_size(&self) -> usize {
        match self {
            Upvalue::Open(_) => 0,
            Upvalue::Closed(_) => std::mem::size_of::<Value>(),
        }
    }
}

// ── ObjNative ────────────────────────────────────────────────────────────────

/// A native (Rust) function callable from Aura.
pub struct ObjNative {
    /// The function's name (for display / stack traces).
    pub name: String,
    /// The function pointer.
    pub func: NativeFn,
}

impl fmt::Debug for ObjNative {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<native {}>", self.name)
    }
}

/// The type signature of a native function.
///
/// `args` is the slice of arguments passed by the caller.
/// Returns a `Value` or a runtime error string.
pub type NativeFn = fn(args: &[Value]) -> Result<Value, String>;

impl GcTrace for ObjNative {
    fn trace(&self, _heap: &mut GcHeap) {}
    fn heap_size(&self) -> usize {
        self.name.capacity()
    }
}

// ── ObjModule ─────────────────────────────────────────────────────────────────

/// A loaded module namespace.
#[derive(Debug)]
pub struct ObjModule {
    /// The module's canonical path/name.
    pub name: String,
    /// The exported bindings.
    pub exports: HashMap<String, Value>,
}

impl GcTrace for ObjModule {
    fn trace(&self, heap: &mut GcHeap) {
        for v in self.exports.values() {
            v.trace(heap);
        }
    }
    fn heap_size(&self) -> usize {
        self.exports.capacity() * (std::mem::size_of::<String>() + std::mem::size_of::<Value>())
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Convenience constructors
// ─────────────────────────────────────────────────────────────────────────────

impl Value {
    /// Allocate a new string value on the GC heap.
    pub fn new_str(heap: &mut GcHeap, s: impl Into<String>) -> Value {
        Value::Str(heap.alloc(ObjString { value: s.into() }))
    }

    /// Allocate a new list value.
    pub fn new_list(heap: &mut GcHeap, items: Vec<Value>) -> Value {
        Value::List(heap.alloc(ObjList {
            items: RefCell::new(items),
        }))
    }

    /// Allocate a new dict value.
    pub fn new_dict(heap: &mut GcHeap, map: HashMap<String, Value>) -> Value {
        Value::Dict(heap.alloc(ObjDict {
            map: RefCell::new(map),
        }))
    }

    /// Allocate a new tuple value.
    pub fn new_tuple(heap: &mut GcHeap, items: Vec<Value>) -> Value {
        Value::Tuple(heap.alloc(ObjTuple { items }))
    }

    /// Allocate a new struct value.
    pub fn new_struct(
        heap: &mut GcHeap,
        type_name: impl Into<String>,
        fields: Vec<(String, Value)>,
    ) -> Value {
        Value::Struct(heap.alloc(ObjStruct {
            type_name: type_name.into(),
            fields,
        }))
    }

    /// Allocate a closure.
    pub fn new_closure(heap: &mut GcHeap, proto: FnProto, upvalues: Vec<Upvalue>) -> Value {
        Value::Closure(heap.alloc(ObjClosure { proto, upvalues }))
    }

    /// Allocate a native function.
    pub fn new_native(heap: &mut GcHeap, name: impl Into<String>, func: NativeFn) -> Value {
        Value::Native(heap.alloc(ObjNative {
            name: name.into(),
            func,
        }))
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_value_display() {
        assert_eq!(format!("{}", Value::Int(42)), "42");
        assert_eq!(format!("{}", Value::Float(3.14)), "3.14");
        assert_eq!(format!("{}", Value::Bool(true)), "true");
        assert_eq!(format!("{}", Value::Null), "null");
    }

    #[test]
    fn test_value_truthiness() {
        assert!(!Value::Null.is_truthy());
        assert!(!Value::Bool(false).is_truthy());
        assert!(Value::Bool(true).is_truthy());
        assert!(!Value::Int(0).is_truthy());
        assert!(Value::Int(1).is_truthy());
    }

    #[test]
    fn test_string_alloc() {
        let mut heap = GcHeap::new();
        let v = Value::new_str(&mut heap, "hello");
        assert_eq!(format!("{v}"), "hello");
    }

    #[test]
    fn test_value_equality() {
        assert_eq!(Value::Int(1), Value::Int(1));
        assert_ne!(Value::Int(1), Value::Int(2));
        assert_eq!(Value::Int(3), Value::Float(3.0));
        assert_eq!(Value::Float(3.0), Value::Int(3));
    }
}
