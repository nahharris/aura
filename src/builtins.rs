//! Native (Rust) built-in functions for the Aura VM.
//!
//! This module provides the [`register_all`] function that registers all
//! built-in native functions into a [`Vm`] instance.  Each native is a plain
//! Rust function with the signature `fn(&[Value]) -> Result<Value, String>`.
//!
//! # Organisation
//!
//! Builtins are grouped by domain:
//!
//! | Group | Functions |
//! |-------|-----------|
//! | Core  | `print`, `println`, `type_of`, `to_str`, `to_int`, `to_float`, `to_bool` |
//! | I/O   | `read_line` |
//! | String | `str_len`, `str_upper`, `str_lower`, `str_trim`, `str_starts_with`, `str_ends_with`, `str_contains`, `str_split`, `str_join`, `str_replace`, `str_slice`, `str_find`, `str_repeat`, `str_chars` |
//! | List  | `list_len`, `list_push`, `list_pop`, `list_insert`, `list_remove`, `list_contains`, `list_reverse`, `list_sort`, `list_map`, `list_filter`, `list_reduce`, `list_concat`, `list_slice` |
//! | Dict  | `dict_keys`, `dict_values`, `dict_entries`, `dict_has`, `dict_delete`, `dict_len`, `dict_merge` |
//! | Math  | `math_abs`, `math_floor`, `math_ceil`, `math_round`, `math_sqrt`, `math_pow`, `math_log`, `math_log2`, `math_log10`, `math_sin`, `math_cos`, `math_tan`, `math_min`, `math_max`, `math_clamp`, `math_random` |
//! | OS    | `os_args`, `os_env`, `os_exit`, `os_read_file`, `os_write_file`, `os_append_file`, `os_delete_file`, `os_exists`, `os_is_file`, `os_is_dir`, `os_mkdir`, `os_ls`, `os_cwd`, `os_now` |
//! | Net   | `net_tcp_connect`, `net_tcp_listen`, `net_tcp_accept`, `net_tcp_send`, `net_tcp_recv`, `net_tcp_close`, `net_udp_bind`, `net_udp_send`, `net_udp_recv`, `net_udp_close`, `net_http_get`, `net_http_post` |

use crate::value::Value;
use crate::vm::Vm;

// ─────────────────────────────────────────────────────────────────────────────
// Registration entry point
// ─────────────────────────────────────────────────────────────────────────────

/// Register all built-in native functions into `vm`.
///
/// After this call every built-in is available as a global variable with the
/// same name as the registered identifier.
pub fn register_all(vm: &mut Vm) {
    // ── Core ──────────────────────────────────────────────────────────────────
    vm.register_native("print", core_print);
    vm.register_native("println", core_println);
    vm.register_native("eprint", core_eprint);
    vm.register_native("eprintln", core_eprintln);
    vm.register_native("type_of", core_type_of);
    vm.register_native("to_str", core_to_str);
    vm.register_native("to_int", core_to_int);
    vm.register_native("to_float", core_to_float);
    vm.register_native("to_bool", core_to_bool);
    vm.register_native("is_null", core_is_null);
    vm.register_native("assert", core_assert);
    vm.register_native("panic", core_panic);

    // ── I/O ───────────────────────────────────────────────────────────────────
    vm.register_native("read_line", io_read_line);

    // ── String ────────────────────────────────────────────────────────────────
    vm.register_native("str_len", str_len);
    vm.register_native("str_upper", str_upper);
    vm.register_native("str_lower", str_lower);
    vm.register_native("str_trim", str_trim);
    vm.register_native("str_trim_start", str_trim_start);
    vm.register_native("str_trim_end", str_trim_end);
    vm.register_native("str_starts_with", str_starts_with);
    vm.register_native("str_ends_with", str_ends_with);
    vm.register_native("str_contains", str_contains);
    vm.register_native("str_split", str_split);
    vm.register_native("str_join", str_join);
    vm.register_native("str_replace", str_replace);
    vm.register_native("str_slice", str_slice);
    vm.register_native("str_find", str_find);
    vm.register_native("str_repeat", str_repeat);
    vm.register_native("str_chars", str_chars);
    vm.register_native("str_bytes", str_bytes);
    vm.register_native("str_from_chars", str_from_chars);
    vm.register_native("str_parse_int", str_parse_int);
    vm.register_native("str_parse_float", str_parse_float);

    // ── List ─────────────────────────────────────────────────────────────────
    vm.register_native("list_len", list_len);
    vm.register_native("list_push", list_push);
    vm.register_native("list_pop", list_pop);
    vm.register_native("list_insert", list_insert);
    vm.register_native("list_remove", list_remove);
    vm.register_native("list_contains", list_contains);
    vm.register_native("list_reverse", list_reverse);
    vm.register_native("list_sort", list_sort);
    vm.register_native("list_concat", list_concat);
    vm.register_native("list_slice", list_slice);
    vm.register_native("list_first", list_first);
    vm.register_native("list_last", list_last);
    vm.register_native("list_flatten", list_flatten);
    vm.register_native("list_range", list_range);
    vm.register_native("list_index_of", list_index_of);

    // ── Dict ─────────────────────────────────────────────────────────────────
    vm.register_native("dict_keys", dict_keys);
    vm.register_native("dict_values", dict_values);
    vm.register_native("dict_entries", dict_entries);
    vm.register_native("dict_has", dict_has);
    vm.register_native("dict_delete", dict_delete);
    vm.register_native("dict_len", dict_len);
    vm.register_native("dict_merge", dict_merge);

    // ── Math ─────────────────────────────────────────────────────────────────
    vm.register_native("math_abs", math_abs);
    vm.register_native("math_floor", math_floor);
    vm.register_native("math_ceil", math_ceil);
    vm.register_native("math_round", math_round);
    vm.register_native("math_sqrt", math_sqrt);
    vm.register_native("math_pow", math_pow);
    vm.register_native("math_log", math_log);
    vm.register_native("math_log2", math_log2);
    vm.register_native("math_log10", math_log10);
    vm.register_native("math_sin", math_sin);
    vm.register_native("math_cos", math_cos);
    vm.register_native("math_tan", math_tan);
    vm.register_native("math_asin", math_asin);
    vm.register_native("math_acos", math_acos);
    vm.register_native("math_atan", math_atan);
    vm.register_native("math_atan2", math_atan2);
    vm.register_native("math_min", math_min);
    vm.register_native("math_max", math_max);
    vm.register_native("math_clamp", math_clamp);
    vm.register_native("math_random", math_random);
    vm.register_native("math_pi", math_pi);
    vm.register_native("math_e", math_e);
    vm.register_native("math_inf", math_inf);
    vm.register_native("math_is_nan", math_is_nan);
    vm.register_native("math_is_inf", math_is_inf);
    vm.register_native("math_trunc", math_trunc);
    vm.register_native("math_fract", math_fract);
    vm.register_native("math_sign", math_sign);

    // ── OS ───────────────────────────────────────────────────────────────────
    vm.register_native("os_args", os_args);
    vm.register_native("os_env", os_env);
    vm.register_native("os_exit", os_exit);
    vm.register_native("os_read_file", os_read_file);
    vm.register_native("os_write_file", os_write_file);
    vm.register_native("os_append_file", os_append_file);
    vm.register_native("os_delete_file", os_delete_file);
    vm.register_native("os_exists", os_exists);
    vm.register_native("os_is_file", os_is_file);
    vm.register_native("os_is_dir", os_is_dir);
    vm.register_native("os_mkdir", os_mkdir);
    vm.register_native("os_ls", os_ls);
    vm.register_native("os_cwd", os_cwd);
    vm.register_native("os_now", os_now);
    vm.register_native("os_sleep", os_sleep);

    // ── Net ──────────────────────────────────────────────────────────────────
    vm.register_native("net_tcp_connect", net_tcp_connect);
    vm.register_native("net_tcp_listen", net_tcp_listen);
    vm.register_native("net_tcp_accept", net_tcp_accept);
    vm.register_native("net_tcp_send", net_tcp_send);
    vm.register_native("net_tcp_recv", net_tcp_recv);
    vm.register_native("net_tcp_close", net_tcp_close);
    vm.register_native("net_udp_bind", net_udp_bind);
    vm.register_native("net_udp_send_to", net_udp_send_to);
    vm.register_native("net_udp_recv_from", net_udp_recv_from);
    vm.register_native("net_udp_close", net_udp_close);
    vm.register_native("net_http_get", net_http_get);
    vm.register_native("net_http_post", net_http_post);
}

// ─────────────────────────────────────────────────────────────────────────────
// Helpers
// ─────────────────────────────────────────────────────────────────────────────

/// Expect exactly `n` arguments; return an error message otherwise.
fn expect_args(name: &str, args: &[Value], n: usize) -> Result<(), String> {
    if args.len() != n {
        Err(format!(
            "{name} expects {n} argument{}, got {}",
            if n == 1 { "" } else { "s" },
            args.len()
        ))
    } else {
        Ok(())
    }
}

/// Expect at least `min` arguments.
fn expect_at_least(name: &str, args: &[Value], min: usize) -> Result<(), String> {
    if args.len() < min {
        Err(format!(
            "{name} expects at least {min} argument(s), got {}",
            args.len()
        ))
    } else {
        Ok(())
    }
}

/// Extract a `&str` from a `Value::Str`.  The pointer is valid as long as the
/// value lives, which it does for the duration of the native call.
fn get_str<'a>(val: &'a Value, pos: &str) -> Result<&'a str, String> {
    match val {
        Value::Str(s) => Ok(unsafe { &s.as_ref().value }),
        other => Err(format!("{pos} must be a String, got {}", other.type_name())),
    }
}

/// Extract an `i64` from an `Int` value.
fn get_int(val: &Value, pos: &str) -> Result<i64, String> {
    match val {
        Value::Int(n) => Ok(*n),
        other => Err(format!("{pos} must be an Int, got {}", other.type_name())),
    }
}

/// Extract an `f64` (widening `Int` → `Float`).
fn get_float(val: &Value, pos: &str) -> Result<f64, String> {
    match val {
        Value::Float(f) => Ok(*f),
        Value::Int(n) => Ok(*n as f64),
        other => Err(format!("{pos} must be a number, got {}", other.type_name())),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Core
// ─────────────────────────────────────────────────────────────────────────────

/// `print(value...)` — print values separated by spaces, no trailing newline.
fn core_print(args: &[Value]) -> Result<Value, String> {
    let parts: Vec<String> = args.iter().map(|v| format!("{v}")).collect();
    print!("{}", parts.join(" "));
    Ok(Value::Null)
}

/// `println(value...)` — print values separated by spaces, with trailing newline.
fn core_println(args: &[Value]) -> Result<Value, String> {
    let parts: Vec<String> = args.iter().map(|v| format!("{v}")).collect();
    println!("{}", parts.join(" "));
    Ok(Value::Null)
}

/// `eprint(value...)` — like `print` but to stderr.
fn core_eprint(args: &[Value]) -> Result<Value, String> {
    let parts: Vec<String> = args.iter().map(|v| format!("{v}")).collect();
    eprint!("{}", parts.join(" "));
    Ok(Value::Null)
}

/// `eprintln(value...)` — like `println` but to stderr.
fn core_eprintln(args: &[Value]) -> Result<Value, String> {
    let parts: Vec<String> = args.iter().map(|v| format!("{v}")).collect();
    eprintln!("{}", parts.join(" "));
    Ok(Value::Null)
}

/// `type_of(value)` — return the type name as a string.
fn core_type_of(args: &[Value]) -> Result<Value, String> {
    expect_args("type_of", args, 1)?;
    let type_name: &'static str = match &args[0] {
        Value::Int(_) => "Int",
        Value::Float(_) => "Float",
        Value::Bool(_) => "Bool",
        Value::Null => "Null",
        Value::Str(_) => "String",
        Value::List(_) => "List",
        Value::Dict(_) => "Dict",
        Value::Tuple(_) => "Tuple",
        Value::Struct(_) => "Struct",
        Value::Closure(_) => "Closure",
        Value::Native(_) => "Native",
        Value::Module(_) => "Module",
    };
    Ok(mk_str(type_name))
}

/// `to_str(value)` — convert any value to its string representation.
fn core_to_str(args: &[Value]) -> Result<Value, String> {
    expect_args("to_str", args, 1)?;
    Ok(mk_str(format!("{}", args[0])))
}

/// `to_int(value)` — convert value to integer.
fn core_to_int(args: &[Value]) -> Result<Value, String> {
    expect_args("to_int", args, 1)?;
    match &args[0] {
        Value::Int(n) => Ok(Value::Int(*n)),
        Value::Float(f) => Ok(Value::Int(*f as i64)),
        Value::Bool(b) => Ok(Value::Int(if *b { 1 } else { 0 })),
        Value::Str(s) => {
            let s = unsafe { &s.as_ref().value };
            s.trim()
                .parse::<i64>()
                .map(Value::Int)
                .map_err(|_| format!("cannot convert {:?} to Int", s))
        }
        other => Err(format!("cannot convert {} to Int", other.type_name())),
    }
}

/// `to_float(value)` — convert value to float.
fn core_to_float(args: &[Value]) -> Result<Value, String> {
    expect_args("to_float", args, 1)?;
    match &args[0] {
        Value::Float(f) => Ok(Value::Float(*f)),
        Value::Int(n) => Ok(Value::Float(*n as f64)),
        Value::Bool(b) => Ok(Value::Float(if *b { 1.0 } else { 0.0 })),
        Value::Str(s) => {
            let s = unsafe { &s.as_ref().value };
            s.trim()
                .parse::<f64>()
                .map(Value::Float)
                .map_err(|_| format!("cannot convert {:?} to Float", s))
        }
        other => Err(format!("cannot convert {} to Float", other.type_name())),
    }
}

/// `to_bool(value)` — convert value to bool using truthiness rules.
fn core_to_bool(args: &[Value]) -> Result<Value, String> {
    expect_args("to_bool", args, 1)?;
    Ok(Value::Bool(args[0].is_truthy()))
}

/// `is_null(value)` — return `true` if value is null.
fn core_is_null(args: &[Value]) -> Result<Value, String> {
    expect_args("is_null", args, 1)?;
    Ok(Value::Bool(args[0].is_null()))
}

/// `assert(cond, msg?)` — panic if condition is falsy.
fn core_assert(args: &[Value]) -> Result<Value, String> {
    expect_at_least("assert", args, 1)?;
    if !args[0].is_truthy() {
        let msg = if args.len() >= 2 {
            format!("{}", args[1])
        } else {
            "assertion failed".to_string()
        };
        return Err(msg);
    }
    Ok(Value::Null)
}

/// `panic(msg)` — raise an unconditional runtime error.
fn core_panic(args: &[Value]) -> Result<Value, String> {
    let msg = if args.is_empty() {
        "explicit panic".to_string()
    } else {
        format!("{}", args[0])
    };
    Err(msg)
}

// ─────────────────────────────────────────────────────────────────────────────
// I/O
// ─────────────────────────────────────────────────────────────────────────────

/// `read_line()` — read a line from stdin, returning it (without the newline).
fn io_read_line(args: &[Value]) -> Result<Value, String> {
    expect_args("read_line", args, 0)?;
    let mut buf = String::new();
    std::io::stdin()
        .read_line(&mut buf)
        .map_err(|e| format!("read_line: {e}"))?;
    // Strip trailing newline.
    if buf.ends_with('\n') {
        buf.pop();
        if buf.ends_with('\r') {
            buf.pop();
        }
    }
    Ok(mk_str(buf))
}

// ─────────────────────────────────────────────────────────────────────────────
// String builtins
// ─────────────────────────────────────────────────────────────────────────────

/// Allocate a new string value on the builtin thread-local heap.
fn mk_str(s: impl Into<String>) -> Value {
    thread_local! {
        static STR_HEAP: std::cell::UnsafeCell<crate::gc::GcHeap> =
            std::cell::UnsafeCell::new(crate::gc::GcHeap::new());
    }
    STR_HEAP.with(|h| {
        let heap = unsafe { &mut *h.get() };
        crate::value::Value::new_str(heap, s)
    })
}

/// Allocate a new list value on the builtin thread-local heap.
fn mk_list(items: Vec<Value>) -> Value {
    thread_local! {
        static LIST_HEAP: std::cell::UnsafeCell<crate::gc::GcHeap> =
            std::cell::UnsafeCell::new(crate::gc::GcHeap::new());
    }
    LIST_HEAP.with(|h| {
        let heap = unsafe { &mut *h.get() };
        crate::value::Value::new_list(heap, items)
    })
}

fn str_len(args: &[Value]) -> Result<Value, String> {
    expect_args("str_len", args, 1)?;
    let s = get_str(&args[0], "argument 1")?;
    Ok(Value::Int(s.chars().count() as i64))
}

fn str_upper(args: &[Value]) -> Result<Value, String> {
    expect_args("str_upper", args, 1)?;
    let s = get_str(&args[0], "argument 1")?;
    Ok(mk_str(s.to_uppercase()))
}

fn str_lower(args: &[Value]) -> Result<Value, String> {
    expect_args("str_lower", args, 1)?;
    let s = get_str(&args[0], "argument 1")?;
    Ok(mk_str(s.to_lowercase()))
}

fn str_trim(args: &[Value]) -> Result<Value, String> {
    expect_args("str_trim", args, 1)?;
    let s = get_str(&args[0], "argument 1")?;
    Ok(mk_str(s.trim().to_string()))
}

fn str_trim_start(args: &[Value]) -> Result<Value, String> {
    expect_args("str_trim_start", args, 1)?;
    let s = get_str(&args[0], "argument 1")?;
    Ok(mk_str(s.trim_start().to_string()))
}

fn str_trim_end(args: &[Value]) -> Result<Value, String> {
    expect_args("str_trim_end", args, 1)?;
    let s = get_str(&args[0], "argument 1")?;
    Ok(mk_str(s.trim_end().to_string()))
}

fn str_starts_with(args: &[Value]) -> Result<Value, String> {
    expect_args("str_starts_with", args, 2)?;
    let s = get_str(&args[0], "argument 1")?;
    let prefix = get_str(&args[1], "argument 2")?;
    Ok(Value::Bool(s.starts_with(prefix)))
}

fn str_ends_with(args: &[Value]) -> Result<Value, String> {
    expect_args("str_ends_with", args, 2)?;
    let s = get_str(&args[0], "argument 1")?;
    let suffix = get_str(&args[1], "argument 2")?;
    Ok(Value::Bool(s.ends_with(suffix)))
}

fn str_contains(args: &[Value]) -> Result<Value, String> {
    expect_args("str_contains", args, 2)?;
    let s = get_str(&args[0], "argument 1")?;
    let needle = get_str(&args[1], "argument 2")?;
    Ok(Value::Bool(s.contains(needle)))
}

fn str_split(args: &[Value]) -> Result<Value, String> {
    expect_args("str_split", args, 2)?;
    let s = get_str(&args[0], "argument 1")?;
    let delim = get_str(&args[1], "argument 2")?;
    let parts: Vec<Value> = s.split(delim).map(|p| mk_str(p.to_string())).collect();
    Ok(mk_list(parts))
}

fn str_join(args: &[Value]) -> Result<Value, String> {
    expect_args("str_join", args, 2)?;
    let sep = get_str(&args[0], "argument 1")?;
    match &args[1] {
        Value::List(l) => {
            let items = unsafe { l.as_ref() };
            let parts: Vec<String> = items
                .items
                .borrow()
                .iter()
                .map(|v| format!("{v}"))
                .collect();
            Ok(mk_str(parts.join(sep)))
        }
        other => Err(format!(
            "str_join argument 2 must be a List, got {}",
            other.type_name()
        )),
    }
}

fn str_replace(args: &[Value]) -> Result<Value, String> {
    expect_args("str_replace", args, 3)?;
    let s = get_str(&args[0], "argument 1")?;
    let from = get_str(&args[1], "argument 2")?;
    let to = get_str(&args[2], "argument 3")?;
    Ok(mk_str(s.replace(from, to)))
}

fn str_slice(args: &[Value]) -> Result<Value, String> {
    expect_args("str_slice", args, 3)?;
    let s = get_str(&args[0], "argument 1")?;
    let start = get_int(&args[1], "argument 2")? as usize;
    let end = get_int(&args[2], "argument 3")? as usize;
    let chars: Vec<char> = s.chars().collect();
    let start = start.min(chars.len());
    let end = end.min(chars.len());
    let sliced: String = chars[start..end].iter().collect();
    Ok(mk_str(sliced))
}

fn str_find(args: &[Value]) -> Result<Value, String> {
    expect_args("str_find", args, 2)?;
    let s = get_str(&args[0], "argument 1")?;
    let needle = get_str(&args[1], "argument 2")?;
    match s.find(needle) {
        Some(byte_idx) => {
            // Convert byte index to char index.
            let char_idx = s[..byte_idx].chars().count() as i64;
            Ok(Value::Int(char_idx))
        }
        None => Ok(Value::Int(-1)),
    }
}

fn str_repeat(args: &[Value]) -> Result<Value, String> {
    expect_args("str_repeat", args, 2)?;
    let s = get_str(&args[0], "argument 1")?;
    let n = get_int(&args[1], "argument 2")?;
    if n < 0 {
        return Ok(mk_str("".to_string()));
    }
    Ok(mk_str(s.repeat(n as usize)))
}

fn str_chars(args: &[Value]) -> Result<Value, String> {
    expect_args("str_chars", args, 1)?;
    let s = get_str(&args[0], "argument 1")?;
    let chars: Vec<Value> = s.chars().map(|c| mk_str(c.to_string())).collect();
    Ok(mk_list(chars))
}

fn str_bytes(args: &[Value]) -> Result<Value, String> {
    expect_args("str_bytes", args, 1)?;
    let s = get_str(&args[0], "argument 1")?;
    let bytes: Vec<Value> = s.bytes().map(|b| Value::Int(b as i64)).collect();
    Ok(mk_list(bytes))
}

fn str_from_chars(args: &[Value]) -> Result<Value, String> {
    expect_args("str_from_chars", args, 1)?;
    match &args[0] {
        Value::List(l) => {
            let items = unsafe { l.as_ref() };
            let mut s = String::new();
            for v in items.items.borrow().iter() {
                match v {
                    Value::Str(cs) => {
                        let c = unsafe { &cs.as_ref().value };
                        s.push_str(c);
                    }
                    Value::Int(n) => {
                        if let Some(c) = char::from_u32(*n as u32) {
                            s.push(c);
                        } else {
                            return Err(format!("str_from_chars: invalid code point {n}"));
                        }
                    }
                    other => {
                        return Err(format!(
                            "str_from_chars: expected String or Int, got {}",
                            other.type_name()
                        ))
                    }
                }
            }
            Ok(mk_str(s))
        }
        other => Err(format!(
            "str_from_chars argument 1 must be a List, got {}",
            other.type_name()
        )),
    }
}

fn str_parse_int(args: &[Value]) -> Result<Value, String> {
    expect_args("str_parse_int", args, 1)?;
    let s = get_str(&args[0], "argument 1")?;
    s.trim()
        .parse::<i64>()
        .map(Value::Int)
        .map_err(|_| format!("str_parse_int: cannot parse {:?}", s))
}

fn str_parse_float(args: &[Value]) -> Result<Value, String> {
    expect_args("str_parse_float", args, 1)?;
    let s = get_str(&args[0], "argument 1")?;
    s.trim()
        .parse::<f64>()
        .map(Value::Float)
        .map_err(|_| format!("str_parse_float: cannot parse {:?}", s))
}

// ─────────────────────────────────────────────────────────────────────────────
// List builtins
// ─────────────────────────────────────────────────────────────────────────────

fn list_len(args: &[Value]) -> Result<Value, String> {
    expect_args("list_len", args, 1)?;
    match &args[0] {
        Value::List(l) => {
            let n = unsafe { l.as_ref() }.items.borrow().len();
            Ok(Value::Int(n as i64))
        }
        other => Err(format!(
            "list_len argument 1 must be a List, got {}",
            other.type_name()
        )),
    }
}

fn list_push(args: &[Value]) -> Result<Value, String> {
    expect_args("list_push", args, 2)?;
    match &args[0] {
        Value::List(l) => {
            unsafe { l.as_ref() }
                .items
                .borrow_mut()
                .push(args[1].clone());
            Ok(Value::Null)
        }
        other => Err(format!(
            "list_push argument 1 must be a List, got {}",
            other.type_name()
        )),
    }
}

fn list_pop(args: &[Value]) -> Result<Value, String> {
    expect_args("list_pop", args, 1)?;
    match &args[0] {
        Value::List(l) => {
            let val = unsafe { l.as_ref() }
                .items
                .borrow_mut()
                .pop()
                .unwrap_or(Value::Null);
            Ok(val)
        }
        other => Err(format!(
            "list_pop argument 1 must be a List, got {}",
            other.type_name()
        )),
    }
}

fn list_insert(args: &[Value]) -> Result<Value, String> {
    expect_args("list_insert", args, 3)?;
    match &args[0] {
        Value::List(l) => {
            let idx = get_int(&args[1], "argument 2")? as usize;
            let val = args[2].clone();
            let mut items = unsafe { l.as_ref() }.items.borrow_mut();
            let idx = idx.min(items.len());
            items.insert(idx, val);
            Ok(Value::Null)
        }
        other => Err(format!(
            "list_insert argument 1 must be a List, got {}",
            other.type_name()
        )),
    }
}

fn list_remove(args: &[Value]) -> Result<Value, String> {
    expect_args("list_remove", args, 2)?;
    match &args[0] {
        Value::List(l) => {
            let idx = get_int(&args[1], "argument 2")? as usize;
            let mut items = unsafe { l.as_ref() }.items.borrow_mut();
            if idx < items.len() {
                Ok(items.remove(idx))
            } else {
                Err(format!(
                    "list_remove: index {idx} out of bounds (len {})",
                    items.len()
                ))
            }
        }
        other => Err(format!(
            "list_remove argument 1 must be a List, got {}",
            other.type_name()
        )),
    }
}

fn list_contains(args: &[Value]) -> Result<Value, String> {
    expect_args("list_contains", args, 2)?;
    match &args[0] {
        Value::List(l) => {
            let found = unsafe { l.as_ref() }.items.borrow().contains(&args[1]);
            Ok(Value::Bool(found))
        }
        other => Err(format!(
            "list_contains argument 1 must be a List, got {}",
            other.type_name()
        )),
    }
}

fn list_reverse(args: &[Value]) -> Result<Value, String> {
    expect_args("list_reverse", args, 1)?;
    match &args[0] {
        Value::List(l) => {
            let items: Vec<Value> = unsafe { l.as_ref() }
                .items
                .borrow()
                .iter()
                .rev()
                .cloned()
                .collect();
            Ok(mk_list(items))
        }
        other => Err(format!(
            "list_reverse argument 1 must be a List, got {}",
            other.type_name()
        )),
    }
}

fn list_sort(args: &[Value]) -> Result<Value, String> {
    expect_args("list_sort", args, 1)?;
    match &args[0] {
        Value::List(l) => {
            let mut items: Vec<Value> = unsafe { l.as_ref() }.items.borrow().clone();
            // Sort numeric / string items; mixed types put nulls last.
            items.sort_by(|a, b| match (a, b) {
                (Value::Int(x), Value::Int(y)) => x.cmp(y),
                (Value::Float(x), Value::Float(y)) => {
                    x.partial_cmp(y).unwrap_or(std::cmp::Ordering::Equal)
                }
                (Value::Int(x), Value::Float(y)) => (*x as f64)
                    .partial_cmp(y)
                    .unwrap_or(std::cmp::Ordering::Equal),
                (Value::Float(x), Value::Int(y)) => x
                    .partial_cmp(&(*y as f64))
                    .unwrap_or(std::cmp::Ordering::Equal),
                (Value::Str(a), Value::Str(b)) => {
                    let a = unsafe { &a.as_ref().value };
                    let b = unsafe { &b.as_ref().value };
                    a.cmp(b)
                }
                (Value::Null, Value::Null) => std::cmp::Ordering::Equal,
                (Value::Null, _) => std::cmp::Ordering::Greater,
                (_, Value::Null) => std::cmp::Ordering::Less,
                _ => std::cmp::Ordering::Equal,
            });
            Ok(mk_list(items))
        }
        other => Err(format!(
            "list_sort argument 1 must be a List, got {}",
            other.type_name()
        )),
    }
}

fn list_concat(args: &[Value]) -> Result<Value, String> {
    expect_args("list_concat", args, 2)?;
    let a = match &args[0] {
        Value::List(l) => unsafe { l.as_ref() }.items.borrow().clone(),
        other => {
            return Err(format!(
                "list_concat argument 1 must be a List, got {}",
                other.type_name()
            ))
        }
    };
    let b = match &args[1] {
        Value::List(l) => unsafe { l.as_ref() }.items.borrow().clone(),
        other => {
            return Err(format!(
                "list_concat argument 2 must be a List, got {}",
                other.type_name()
            ))
        }
    };
    let mut result = a;
    result.extend(b);
    Ok(mk_list(result))
}

fn list_slice(args: &[Value]) -> Result<Value, String> {
    expect_args("list_slice", args, 3)?;
    match &args[0] {
        Value::List(l) => {
            let items = unsafe { l.as_ref() }.items.borrow();
            let start = get_int(&args[1], "argument 2")? as usize;
            let end = get_int(&args[2], "argument 3")? as usize;
            let start = start.min(items.len());
            let end = end.min(items.len());
            let sliced: Vec<Value> = items[start..end].to_vec();
            Ok(mk_list(sliced))
        }
        other => Err(format!(
            "list_slice argument 1 must be a List, got {}",
            other.type_name()
        )),
    }
}

fn list_first(args: &[Value]) -> Result<Value, String> {
    expect_args("list_first", args, 1)?;
    match &args[0] {
        Value::List(l) => {
            let val = unsafe { l.as_ref() }
                .items
                .borrow()
                .first()
                .cloned()
                .unwrap_or(Value::Null);
            Ok(val)
        }
        other => Err(format!(
            "list_first argument 1 must be a List, got {}",
            other.type_name()
        )),
    }
}

fn list_last(args: &[Value]) -> Result<Value, String> {
    expect_args("list_last", args, 1)?;
    match &args[0] {
        Value::List(l) => {
            let val = unsafe { l.as_ref() }
                .items
                .borrow()
                .last()
                .cloned()
                .unwrap_or(Value::Null);
            Ok(val)
        }
        other => Err(format!(
            "list_last argument 1 must be a List, got {}",
            other.type_name()
        )),
    }
}

fn list_flatten(args: &[Value]) -> Result<Value, String> {
    expect_args("list_flatten", args, 1)?;
    fn flatten_into(val: &Value, out: &mut Vec<Value>) {
        match val {
            Value::List(l) => {
                for v in unsafe { l.as_ref() }.items.borrow().iter() {
                    flatten_into(v, out);
                }
            }
            other => out.push(other.clone()),
        }
    }
    let mut result = Vec::new();
    flatten_into(&args[0], &mut result);
    Ok(mk_list(result))
}

fn list_range(args: &[Value]) -> Result<Value, String> {
    // list_range(start, end) or list_range(start, end, step)
    expect_at_least("list_range", args, 2)?;
    let start = get_int(&args[0], "argument 1")?;
    let end = get_int(&args[1], "argument 2")?;
    let step = if args.len() >= 3 {
        get_int(&args[2], "argument 3")?
    } else {
        1
    };
    if step == 0 {
        return Err("list_range: step cannot be zero".to_string());
    }
    let mut items = Vec::new();
    let mut i = start;
    while if step > 0 { i < end } else { i > end } {
        items.push(Value::Int(i));
        i += step;
    }
    Ok(mk_list(items))
}

fn list_index_of(args: &[Value]) -> Result<Value, String> {
    expect_args("list_index_of", args, 2)?;
    match &args[0] {
        Value::List(l) => {
            let items = unsafe { l.as_ref() }.items.borrow();
            let idx = items.iter().position(|v| v == &args[1]);
            Ok(Value::Int(idx.map(|i| i as i64).unwrap_or(-1)))
        }
        other => Err(format!(
            "list_index_of argument 1 must be a List, got {}",
            other.type_name()
        )),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Dict builtins
// ─────────────────────────────────────────────────────────────────────────────

fn dict_keys(args: &[Value]) -> Result<Value, String> {
    expect_args("dict_keys", args, 1)?;
    match &args[0] {
        Value::Dict(d) => {
            let keys: Vec<Value> = unsafe { d.as_ref() }
                .map
                .borrow()
                .keys()
                .map(|k| mk_str(k.clone()))
                .collect();
            Ok(mk_list(keys))
        }
        other => Err(format!(
            "dict_keys argument 1 must be a Dict, got {}",
            other.type_name()
        )),
    }
}

fn dict_values(args: &[Value]) -> Result<Value, String> {
    expect_args("dict_values", args, 1)?;
    match &args[0] {
        Value::Dict(d) => {
            let vals: Vec<Value> = unsafe { d.as_ref() }
                .map
                .borrow()
                .values()
                .cloned()
                .collect();
            Ok(mk_list(vals))
        }
        other => Err(format!(
            "dict_values argument 1 must be a Dict, got {}",
            other.type_name()
        )),
    }
}

fn dict_entries(args: &[Value]) -> Result<Value, String> {
    expect_args("dict_entries", args, 1)?;
    match &args[0] {
        Value::Dict(d) => {
            let entries: Vec<Value> = unsafe { d.as_ref() }
                .map
                .borrow()
                .iter()
                .map(|(k, v)| mk_list(vec![mk_str(k.clone()), v.clone()]))
                .collect();
            Ok(mk_list(entries))
        }
        other => Err(format!(
            "dict_entries argument 1 must be a Dict, got {}",
            other.type_name()
        )),
    }
}

fn dict_has(args: &[Value]) -> Result<Value, String> {
    expect_args("dict_has", args, 2)?;
    match &args[0] {
        Value::Dict(d) => {
            let key = get_str(&args[1], "argument 2")?;
            let has = unsafe { d.as_ref() }.map.borrow().contains_key(key);
            Ok(Value::Bool(has))
        }
        other => Err(format!(
            "dict_has argument 1 must be a Dict, got {}",
            other.type_name()
        )),
    }
}

fn dict_delete(args: &[Value]) -> Result<Value, String> {
    expect_args("dict_delete", args, 2)?;
    match &args[0] {
        Value::Dict(d) => {
            let key = get_str(&args[1], "argument 2")?;
            let removed = unsafe { d.as_ref() }
                .map
                .borrow_mut()
                .remove(key)
                .unwrap_or(Value::Null);
            Ok(removed)
        }
        other => Err(format!(
            "dict_delete argument 1 must be a Dict, got {}",
            other.type_name()
        )),
    }
}

fn dict_len(args: &[Value]) -> Result<Value, String> {
    expect_args("dict_len", args, 1)?;
    match &args[0] {
        Value::Dict(d) => {
            let n = unsafe { d.as_ref() }.map.borrow().len();
            Ok(Value::Int(n as i64))
        }
        other => Err(format!(
            "dict_len argument 1 must be a Dict, got {}",
            other.type_name()
        )),
    }
}

fn dict_merge(args: &[Value]) -> Result<Value, String> {
    expect_args("dict_merge", args, 2)?;
    let a = match &args[0] {
        Value::Dict(d) => unsafe { d.as_ref() }.map.borrow().clone(),
        other => {
            return Err(format!(
                "dict_merge argument 1 must be a Dict, got {}",
                other.type_name()
            ))
        }
    };
    let b = match &args[1] {
        Value::Dict(d) => unsafe { d.as_ref() }.map.borrow().clone(),
        other => {
            return Err(format!(
                "dict_merge argument 2 must be a Dict, got {}",
                other.type_name()
            ))
        }
    };
    let mut result = a;
    result.extend(b);
    thread_local! {
        static DICT_HEAP: std::cell::UnsafeCell<crate::gc::GcHeap> =
            std::cell::UnsafeCell::new(crate::gc::GcHeap::new());
    }
    let val = DICT_HEAP.with(|h| {
        let heap = unsafe { &mut *h.get() };
        crate::value::Value::new_dict(heap, result)
    });
    Ok(val)
}

// ─────────────────────────────────────────────────────────────────────────────
// Math builtins
// ─────────────────────────────────────────────────────────────────────────────

fn math_abs(args: &[Value]) -> Result<Value, String> {
    expect_args("math_abs", args, 1)?;
    match &args[0] {
        Value::Int(n) => Ok(Value::Int(n.abs())),
        Value::Float(f) => Ok(Value::Float(f.abs())),
        other => Err(format!(
            "math_abs argument must be a number, got {}",
            other.type_name()
        )),
    }
}

fn math_floor(args: &[Value]) -> Result<Value, String> {
    expect_args("math_floor", args, 1)?;
    Ok(Value::Int(get_float(&args[0], "argument 1")?.floor() as i64))
}

fn math_ceil(args: &[Value]) -> Result<Value, String> {
    expect_args("math_ceil", args, 1)?;
    Ok(Value::Int(get_float(&args[0], "argument 1")?.ceil() as i64))
}

fn math_round(args: &[Value]) -> Result<Value, String> {
    expect_args("math_round", args, 1)?;
    Ok(Value::Int(get_float(&args[0], "argument 1")?.round() as i64))
}

fn math_sqrt(args: &[Value]) -> Result<Value, String> {
    expect_args("math_sqrt", args, 1)?;
    Ok(Value::Float(get_float(&args[0], "argument 1")?.sqrt()))
}

fn math_pow(args: &[Value]) -> Result<Value, String> {
    expect_args("math_pow", args, 2)?;
    let base = get_float(&args[0], "argument 1")?;
    let exp = get_float(&args[1], "argument 2")?;
    Ok(Value::Float(base.powf(exp)))
}

fn math_log(args: &[Value]) -> Result<Value, String> {
    expect_args("math_log", args, 1)?;
    Ok(Value::Float(get_float(&args[0], "argument 1")?.ln()))
}

fn math_log2(args: &[Value]) -> Result<Value, String> {
    expect_args("math_log2", args, 1)?;
    Ok(Value::Float(get_float(&args[0], "argument 1")?.log2()))
}

fn math_log10(args: &[Value]) -> Result<Value, String> {
    expect_args("math_log10", args, 1)?;
    Ok(Value::Float(get_float(&args[0], "argument 1")?.log10()))
}

fn math_sin(args: &[Value]) -> Result<Value, String> {
    expect_args("math_sin", args, 1)?;
    Ok(Value::Float(get_float(&args[0], "argument 1")?.sin()))
}

fn math_cos(args: &[Value]) -> Result<Value, String> {
    expect_args("math_cos", args, 1)?;
    Ok(Value::Float(get_float(&args[0], "argument 1")?.cos()))
}

fn math_tan(args: &[Value]) -> Result<Value, String> {
    expect_args("math_tan", args, 1)?;
    Ok(Value::Float(get_float(&args[0], "argument 1")?.tan()))
}

fn math_asin(args: &[Value]) -> Result<Value, String> {
    expect_args("math_asin", args, 1)?;
    Ok(Value::Float(get_float(&args[0], "argument 1")?.asin()))
}

fn math_acos(args: &[Value]) -> Result<Value, String> {
    expect_args("math_acos", args, 1)?;
    Ok(Value::Float(get_float(&args[0], "argument 1")?.acos()))
}

fn math_atan(args: &[Value]) -> Result<Value, String> {
    expect_args("math_atan", args, 1)?;
    Ok(Value::Float(get_float(&args[0], "argument 1")?.atan()))
}

fn math_atan2(args: &[Value]) -> Result<Value, String> {
    expect_args("math_atan2", args, 2)?;
    let y = get_float(&args[0], "argument 1")?;
    let x = get_float(&args[1], "argument 2")?;
    Ok(Value::Float(y.atan2(x)))
}

fn math_min(args: &[Value]) -> Result<Value, String> {
    expect_args("math_min", args, 2)?;
    let a = get_float(&args[0], "argument 1")?;
    let b = get_float(&args[1], "argument 2")?;
    Ok(Value::Float(a.min(b)))
}

fn math_max(args: &[Value]) -> Result<Value, String> {
    expect_args("math_max", args, 2)?;
    let a = get_float(&args[0], "argument 1")?;
    let b = get_float(&args[1], "argument 2")?;
    Ok(Value::Float(a.max(b)))
}

fn math_clamp(args: &[Value]) -> Result<Value, String> {
    expect_args("math_clamp", args, 3)?;
    let v = get_float(&args[0], "argument 1")?;
    let lo = get_float(&args[1], "argument 2")?;
    let hi = get_float(&args[2], "argument 3")?;
    Ok(Value::Float(v.clamp(lo, hi)))
}

fn math_random(args: &[Value]) -> Result<Value, String> {
    expect_args("math_random", args, 0)?;
    // Simple LCG pseudo-random; no external crate required.
    use std::time::{SystemTime, UNIX_EPOCH};
    static SEED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let mut seed = SEED.load(std::sync::atomic::Ordering::Relaxed);
    if seed == 0 {
        seed = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .subsec_nanos() as u64;
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
    }
    // Xorshift64.
    seed ^= seed << 13;
    seed ^= seed >> 7;
    seed ^= seed << 17;
    SEED.store(seed, std::sync::atomic::Ordering::Relaxed);
    let f = (seed >> 11) as f64 / (u64::MAX >> 11) as f64;
    Ok(Value::Float(f))
}

fn math_pi(args: &[Value]) -> Result<Value, String> {
    expect_args("math_pi", args, 0)?;
    Ok(Value::Float(std::f64::consts::PI))
}

fn math_e(args: &[Value]) -> Result<Value, String> {
    expect_args("math_e", args, 0)?;
    Ok(Value::Float(std::f64::consts::E))
}

fn math_inf(args: &[Value]) -> Result<Value, String> {
    expect_args("math_inf", args, 0)?;
    Ok(Value::Float(f64::INFINITY))
}

fn math_is_nan(args: &[Value]) -> Result<Value, String> {
    expect_args("math_is_nan", args, 1)?;
    Ok(Value::Bool(get_float(&args[0], "argument 1")?.is_nan()))
}

fn math_is_inf(args: &[Value]) -> Result<Value, String> {
    expect_args("math_is_inf", args, 1)?;
    Ok(Value::Bool(
        get_float(&args[0], "argument 1")?.is_infinite(),
    ))
}

fn math_trunc(args: &[Value]) -> Result<Value, String> {
    expect_args("math_trunc", args, 1)?;
    Ok(Value::Float(get_float(&args[0], "argument 1")?.trunc()))
}

fn math_fract(args: &[Value]) -> Result<Value, String> {
    expect_args("math_fract", args, 1)?;
    Ok(Value::Float(get_float(&args[0], "argument 1")?.fract()))
}

fn math_sign(args: &[Value]) -> Result<Value, String> {
    expect_args("math_sign", args, 1)?;
    match &args[0] {
        Value::Int(n) => Ok(Value::Int(n.signum())),
        Value::Float(f) => Ok(Value::Float(if *f > 0.0 {
            1.0
        } else if *f < 0.0 {
            -1.0
        } else {
            0.0
        })),
        other => Err(format!(
            "math_sign argument must be a number, got {}",
            other.type_name()
        )),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// OS builtins
// ─────────────────────────────────────────────────────────────────────────────

fn os_args(args: &[Value]) -> Result<Value, String> {
    expect_args("os_args", args, 0)?;
    let cli_args: Vec<Value> = std::env::args().map(mk_str).collect();
    Ok(mk_list(cli_args))
}

fn os_env(args: &[Value]) -> Result<Value, String> {
    expect_args("os_env", args, 1)?;
    let key = get_str(&args[0], "argument 1")?;
    let val = std::env::var(key).ok();
    Ok(val.map(mk_str).unwrap_or(Value::Null))
}

fn os_exit(args: &[Value]) -> Result<Value, String> {
    let code = if args.is_empty() {
        0
    } else {
        get_int(&args[0], "argument 1")? as i32
    };
    std::process::exit(code);
}

fn os_read_file(args: &[Value]) -> Result<Value, String> {
    expect_args("os_read_file", args, 1)?;
    let path = get_str(&args[0], "argument 1")?;
    std::fs::read_to_string(path)
        .map(mk_str)
        .map_err(|e| format!("os_read_file: {e}"))
}

fn os_write_file(args: &[Value]) -> Result<Value, String> {
    expect_args("os_write_file", args, 2)?;
    let path = get_str(&args[0], "argument 1")?;
    let content = get_str(&args[1], "argument 2")?;
    std::fs::write(path, content).map_err(|e| format!("os_write_file: {e}"))?;
    Ok(Value::Null)
}

fn os_append_file(args: &[Value]) -> Result<Value, String> {
    expect_args("os_append_file", args, 2)?;
    let path = get_str(&args[0], "argument 1")?;
    let content = get_str(&args[1], "argument 2")?;
    use std::io::Write;
    let mut file = std::fs::OpenOptions::new()
        .append(true)
        .create(true)
        .open(path)
        .map_err(|e| format!("os_append_file: {e}"))?;
    file.write_all(content.as_bytes())
        .map_err(|e| format!("os_append_file: {e}"))?;
    Ok(Value::Null)
}

fn os_delete_file(args: &[Value]) -> Result<Value, String> {
    expect_args("os_delete_file", args, 1)?;
    let path = get_str(&args[0], "argument 1")?;
    std::fs::remove_file(path).map_err(|e| format!("os_delete_file: {e}"))?;
    Ok(Value::Null)
}

fn os_exists(args: &[Value]) -> Result<Value, String> {
    expect_args("os_exists", args, 1)?;
    let path = get_str(&args[0], "argument 1")?;
    Ok(Value::Bool(std::path::Path::new(path).exists()))
}

fn os_is_file(args: &[Value]) -> Result<Value, String> {
    expect_args("os_is_file", args, 1)?;
    let path = get_str(&args[0], "argument 1")?;
    Ok(Value::Bool(std::path::Path::new(path).is_file()))
}

fn os_is_dir(args: &[Value]) -> Result<Value, String> {
    expect_args("os_is_dir", args, 1)?;
    let path = get_str(&args[0], "argument 1")?;
    Ok(Value::Bool(std::path::Path::new(path).is_dir()))
}

fn os_mkdir(args: &[Value]) -> Result<Value, String> {
    expect_args("os_mkdir", args, 1)?;
    let path = get_str(&args[0], "argument 1")?;
    std::fs::create_dir_all(path).map_err(|e| format!("os_mkdir: {e}"))?;
    Ok(Value::Null)
}

fn os_ls(args: &[Value]) -> Result<Value, String> {
    expect_args("os_ls", args, 1)?;
    let path = get_str(&args[0], "argument 1")?;
    let entries: Result<Vec<Value>, String> = std::fs::read_dir(path)
        .map_err(|e| format!("os_ls: {e}"))?
        .map(|entry| {
            let entry = entry.map_err(|e| format!("os_ls: {e}"))?;
            Ok(mk_str(entry.file_name().to_string_lossy().into_owned()))
        })
        .collect();
    Ok(mk_list(entries?))
}

fn os_cwd(args: &[Value]) -> Result<Value, String> {
    expect_args("os_cwd", args, 0)?;
    let cwd = std::env::current_dir()
        .map_err(|e| format!("os_cwd: {e}"))?
        .to_string_lossy()
        .into_owned();
    Ok(mk_str(cwd))
}

fn os_now(args: &[Value]) -> Result<Value, String> {
    expect_args("os_now", args, 0)?;
    use std::time::{SystemTime, UNIX_EPOCH};
    let ms = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_millis() as i64)
        .unwrap_or(0);
    Ok(Value::Int(ms))
}

fn os_sleep(args: &[Value]) -> Result<Value, String> {
    expect_args("os_sleep", args, 1)?;
    let ms = get_int(&args[0], "argument 1")?;
    if ms > 0 {
        std::thread::sleep(std::time::Duration::from_millis(ms as u64));
    }
    Ok(Value::Null)
}

// ─────────────────────────────────────────────────────────────────────────────
// Net
// ─────────────────────────────────────────────────────────────────────────────
//
// Sockets are not first-class `Value` types yet, so they are stored in
// thread-local registries keyed by an integer handle (`Value::Int`).  The
// handle is returned to Aura code and passed back on subsequent calls.
//
// TCP stream registry: handle → TcpStream
// TCP listener registry: handle → TcpListener
// UDP socket registry:  handle → UdpSocket

use std::collections::HashMap as StdHashMap;
use std::io::{BufRead, BufReader, Write as IoWrite};
use std::net::{TcpListener, TcpStream, UdpSocket};

thread_local! {
    static TCP_STREAMS: std::cell::RefCell<StdHashMap<i64, TcpStream>> =
        std::cell::RefCell::new(StdHashMap::new());
    static TCP_LISTENERS: std::cell::RefCell<StdHashMap<i64, TcpListener>> =
        std::cell::RefCell::new(StdHashMap::new());
    static UDP_SOCKETS: std::cell::RefCell<StdHashMap<i64, UdpSocket>> =
        std::cell::RefCell::new(StdHashMap::new());
    static NEXT_NET_HANDLE: std::cell::Cell<i64> = const { std::cell::Cell::new(1) };
}

fn next_net_handle() -> i64 {
    NEXT_NET_HANDLE.with(|c| {
        let h = c.get();
        c.set(h + 1);
        h
    })
}

/// `net_tcp_connect(host: String, port: Int) -> Result`
///
/// Open a TCP connection to `host:port`.
/// Returns `.ok(handle)` on success or `.error(msg)` on failure.
fn net_tcp_connect(args: &[Value]) -> Result<Value, String> {
    expect_args("net_tcp_connect", args, 2)?;
    let host = get_str(&args[0], "argument 1 (host)")?.to_string();
    let port = get_int(&args[1], "argument 2 (port)")?;
    if !(1..=65535).contains(&port) {
        return Ok(mk_error(format!("invalid port: {port}")));
    }
    let addr = format!("{host}:{port}");
    match TcpStream::connect(&addr) {
        Ok(stream) => {
            let handle = next_net_handle();
            TCP_STREAMS.with(|m| m.borrow_mut().insert(handle, stream));
            Ok(mk_ok(Value::Int(handle)))
        }
        Err(e) => Ok(mk_error(format!("net_tcp_connect: {e}"))),
    }
}

/// `net_tcp_listen(host: String, port: Int) -> Result`
///
/// Bind a TCP listener on `host:port`.
/// Returns `.ok(handle)` on success or `.error(msg)` on failure.
fn net_tcp_listen(args: &[Value]) -> Result<Value, String> {
    expect_args("net_tcp_listen", args, 2)?;
    let host = get_str(&args[0], "argument 1 (host)")?.to_string();
    let port = get_int(&args[1], "argument 2 (port)")?;
    if !(1..=65535).contains(&port) {
        return Ok(mk_error(format!("invalid port: {port}")));
    }
    let addr = format!("{host}:{port}");
    match TcpListener::bind(&addr) {
        Ok(listener) => {
            let handle = next_net_handle();
            TCP_LISTENERS.with(|m| m.borrow_mut().insert(handle, listener));
            Ok(mk_ok(Value::Int(handle)))
        }
        Err(e) => Ok(mk_error(format!("net_tcp_listen: {e}"))),
    }
}

/// `net_tcp_accept(listener_handle: Int) -> Result`
///
/// Accept one incoming connection on a listener handle.
/// Returns `.ok(stream_handle)` or `.error(msg)`.
fn net_tcp_accept(args: &[Value]) -> Result<Value, String> {
    expect_args("net_tcp_accept", args, 1)?;
    let lh = get_int(&args[0], "argument 1 (listener_handle)")?;
    let result = TCP_LISTENERS.with(|m| {
        let map = m.borrow();
        map.get(&lh).map(|listener| {
            // We need to call accept without holding the borrow.
            // Clone the listener reference is not possible (TcpListener isn't Clone),
            // so we call try_clone to get an owned copy for this one accept.
            listener.try_clone()
        })
    });
    match result {
        None => Ok(mk_error(format!("invalid listener handle: {lh}"))),
        Some(Err(e)) => Ok(mk_error(format!("net_tcp_accept (clone): {e}"))),
        Some(Ok(listener_clone)) => match listener_clone.accept() {
            Ok((stream, _addr)) => {
                let handle = next_net_handle();
                TCP_STREAMS.with(|m| m.borrow_mut().insert(handle, stream));
                Ok(mk_ok(Value::Int(handle)))
            }
            Err(e) => Ok(mk_error(format!("net_tcp_accept: {e}"))),
        },
    }
}

/// `net_tcp_send(handle: Int, data: String) -> Result`
///
/// Write `data` to an open TCP stream.
/// Returns `.ok(bytes_written)` or `.error(msg)`.
fn net_tcp_send(args: &[Value]) -> Result<Value, String> {
    expect_args("net_tcp_send", args, 2)?;
    let handle = get_int(&args[0], "argument 1 (handle)")?;
    let data = get_str(&args[1], "argument 2 (data)")?.to_string();
    let result = TCP_STREAMS.with(|m| {
        let mut map = m.borrow_mut();
        match map.get_mut(&handle) {
            None => Err(format!("invalid TCP stream handle: {handle}")),
            Some(stream) => stream
                .write_all(data.as_bytes())
                .map(|_| data.len() as i64)
                .map_err(|e| format!("net_tcp_send: {e}")),
        }
    });
    match result {
        Ok(n) => Ok(mk_ok(Value::Int(n))),
        Err(e) => Ok(mk_error(e)),
    }
}

/// `net_tcp_recv(handle: Int, max_bytes: Int) -> Result`
///
/// Read up to `max_bytes` from an open TCP stream.
/// Returns `.ok(string)` or `.error(msg)`.
fn net_tcp_recv(args: &[Value]) -> Result<Value, String> {
    expect_args("net_tcp_recv", args, 2)?;
    let handle = get_int(&args[0], "argument 1 (handle)")?;
    let max = get_int(&args[1], "argument 2 (max_bytes)")?;
    if max <= 0 {
        return Ok(mk_error("max_bytes must be > 0".to_string()));
    }
    use std::io::Read;
    let result = TCP_STREAMS.with(|m| {
        let mut map = m.borrow_mut();
        match map.get_mut(&handle) {
            None => Err(format!("invalid TCP stream handle: {handle}")),
            Some(stream) => {
                let mut buf = vec![0u8; max as usize];
                match stream.read(&mut buf) {
                    Ok(n) => Ok(String::from_utf8_lossy(&buf[..n]).into_owned()),
                    Err(e) => Err(format!("net_tcp_recv: {e}")),
                }
            }
        }
    });
    match result {
        Ok(s) => Ok(mk_ok(mk_str(s))),
        Err(e) => Ok(mk_error(e)),
    }
}

/// `net_tcp_close(handle: Int) -> Bool`
///
/// Close and remove the TCP stream (or listener) with the given handle.
/// Returns `true` if the handle was found and closed, `false` otherwise.
fn net_tcp_close(args: &[Value]) -> Result<Value, String> {
    expect_args("net_tcp_close", args, 1)?;
    let handle = get_int(&args[0], "argument 1 (handle)")?;
    let removed_stream = TCP_STREAMS.with(|m| m.borrow_mut().remove(&handle).is_some());
    let removed_listener = TCP_LISTENERS.with(|m| m.borrow_mut().remove(&handle).is_some());
    Ok(Value::Bool(removed_stream || removed_listener))
}

/// `net_udp_bind(host: String, port: Int) -> Result`
///
/// Bind a UDP socket to `host:port`.
/// Returns `.ok(handle)` or `.error(msg)`.
fn net_udp_bind(args: &[Value]) -> Result<Value, String> {
    expect_args("net_udp_bind", args, 2)?;
    let host = get_str(&args[0], "argument 1 (host)")?.to_string();
    let port = get_int(&args[1], "argument 2 (port)")?;
    if !(0..=65535).contains(&port) {
        return Ok(mk_error(format!("invalid port: {port}")));
    }
    let addr = format!("{host}:{port}");
    match UdpSocket::bind(&addr) {
        Ok(sock) => {
            let handle = next_net_handle();
            UDP_SOCKETS.with(|m| m.borrow_mut().insert(handle, sock));
            Ok(mk_ok(Value::Int(handle)))
        }
        Err(e) => Ok(mk_error(format!("net_udp_bind: {e}"))),
    }
}

/// `net_udp_send_to(handle: Int, data: String, host: String, port: Int) -> Result`
///
/// Send a UDP datagram to `host:port`.
/// Returns `.ok(bytes_sent)` or `.error(msg)`.
fn net_udp_send_to(args: &[Value]) -> Result<Value, String> {
    expect_args("net_udp_send_to", args, 4)?;
    let handle = get_int(&args[0], "argument 1 (handle)")?;
    let data = get_str(&args[1], "argument 2 (data)")?.to_string();
    let host = get_str(&args[2], "argument 3 (host)")?.to_string();
    let port = get_int(&args[3], "argument 4 (port)")?;
    let dest = format!("{host}:{port}");
    let result = UDP_SOCKETS.with(|m| {
        let map = m.borrow();
        match map.get(&handle) {
            None => Err(format!("invalid UDP socket handle: {handle}")),
            Some(sock) => sock
                .send_to(data.as_bytes(), &dest)
                .map_err(|e| format!("net_udp_send_to: {e}")),
        }
    });
    match result {
        Ok(n) => Ok(mk_ok(Value::Int(n as i64))),
        Err(e) => Ok(mk_error(e)),
    }
}

/// `net_udp_recv_from(handle: Int, max_bytes: Int) -> Result`
///
/// Receive a UDP datagram.  Returns `.ok([data, sender_addr])` or `.error(msg)`.
/// `sender_addr` is a string `"host:port"`.
fn net_udp_recv_from(args: &[Value]) -> Result<Value, String> {
    expect_args("net_udp_recv_from", args, 2)?;
    let handle = get_int(&args[0], "argument 1 (handle)")?;
    let max = get_int(&args[1], "argument 2 (max_bytes)")?;
    if max <= 0 {
        return Ok(mk_error("max_bytes must be > 0".to_string()));
    }
    let result = UDP_SOCKETS.with(|m| {
        let map = m.borrow();
        match map.get(&handle) {
            None => Err(format!("invalid UDP socket handle: {handle}")),
            Some(sock) => {
                let mut buf = vec![0u8; max as usize];
                sock.recv_from(&mut buf)
                    .map(|(n, addr)| {
                        (
                            String::from_utf8_lossy(&buf[..n]).into_owned(),
                            addr.to_string(),
                        )
                    })
                    .map_err(|e| format!("net_udp_recv_from: {e}"))
            }
        }
    });
    match result {
        Ok((data, addr)) => {
            let pair = mk_list(vec![mk_str(data), mk_str(addr)]);
            Ok(mk_ok(pair))
        }
        Err(e) => Ok(mk_error(e)),
    }
}

/// `net_udp_close(handle: Int) -> Bool`
///
/// Close and remove a UDP socket handle.
/// Returns `true` if found and closed, `false` otherwise.
fn net_udp_close(args: &[Value]) -> Result<Value, String> {
    expect_args("net_udp_close", args, 1)?;
    let handle = get_int(&args[0], "argument 1 (handle)")?;
    Ok(Value::Bool(
        UDP_SOCKETS.with(|m| m.borrow_mut().remove(&handle).is_some()),
    ))
}

/// `net_http_get(url: String) -> Result`
///
/// Perform a basic HTTP GET request.  Handles HTTP/1.0 and HTTP/1.1 over plain
/// TCP (no TLS).  Returns `.ok(body)` or `.error(msg)`.
///
/// The URL must start with `http://`.
fn net_http_get(args: &[Value]) -> Result<Value, String> {
    expect_args("net_http_get", args, 1)?;
    let url = get_str(&args[0], "argument 1 (url)")?.to_string();
    match http_request("GET", &url, None, None) {
        Ok(body) => Ok(mk_ok(mk_str(body))),
        Err(e) => Ok(mk_error(e)),
    }
}

/// `net_http_post(url: String, body: String, content_type: String) -> Result`
///
/// Perform a basic HTTP POST request over plain TCP (no TLS).
/// Returns `.ok(response_body)` or `.error(msg)`.
fn net_http_post(args: &[Value]) -> Result<Value, String> {
    expect_args("net_http_post", args, 3)?;
    let url = get_str(&args[0], "argument 1 (url)")?.to_string();
    let body = get_str(&args[1], "argument 2 (body)")?.to_string();
    let ctype = get_str(&args[2], "argument 3 (content_type)")?.to_string();
    match http_request("POST", &url, Some(&body), Some(&ctype)) {
        Ok(resp) => Ok(mk_ok(mk_str(resp))),
        Err(e) => Ok(mk_error(e)),
    }
}

// ── HTTP helper ───────────────────────────────────────────────────────────────

/// Parse a bare `http://host[:port]/path?query` URL into (host, port, path).
/// Returns `Err(msg)` for unsupported schemes or malformed URLs.
fn parse_http_url(url: &str) -> Result<(String, u16, String), String> {
    let rest = url
        .strip_prefix("http://")
        .ok_or_else(|| format!("net_http: only http:// URLs are supported, got: {url}"))?;
    let (authority, path) = match rest.find('/') {
        Some(idx) => (&rest[..idx], rest[idx..].to_string()),
        None => (rest, "/".to_string()),
    };
    let (host, port) = if let Some(colon) = authority.rfind(':') {
        let p: u16 = authority[colon + 1..]
            .parse()
            .map_err(|_| format!("invalid port in URL: {url}"))?;
        (authority[..colon].to_string(), p)
    } else {
        (authority.to_string(), 80u16)
    };
    if host.is_empty() {
        return Err(format!("empty host in URL: {url}"));
    }
    Ok((host, port, path))
}

/// Minimal HTTP/1.1 request over a plain TCP connection.
/// Follows up to 5 redirects.  Returns the response body as a `String`.
fn http_request(
    method: &str,
    url: &str,
    body: Option<&str>,
    content_type: Option<&str>,
) -> Result<String, String> {
    let mut current_url = url.to_string();
    for _ in 0..5 {
        let (host, port, path) = parse_http_url(&current_url)?;
        let addr = format!("{host}:{port}");
        let mut stream =
            TcpStream::connect(&addr).map_err(|e| format!("net_http: connect {addr}: {e}"))?;

        // Build request
        let mut request = format!(
            "{method} {path} HTTP/1.1\r\nHost: {host}\r\nConnection: close\r\nAccept: */*\r\n"
        );
        if let Some(b) = body {
            let ct = content_type.unwrap_or("application/octet-stream");
            request.push_str(&format!(
                "Content-Type: {ct}\r\nContent-Length: {}\r\n",
                b.len()
            ));
        }
        request.push_str("\r\n");
        if let Some(b) = body {
            request.push_str(b);
        }

        stream
            .write_all(request.as_bytes())
            .map_err(|e| format!("net_http: write: {e}"))?;

        // Read response
        let mut reader = BufReader::new(stream);
        let mut status_line = String::new();
        reader
            .read_line(&mut status_line)
            .map_err(|e| format!("net_http: read status: {e}"))?;
        let status_line = status_line.trim_end().to_string();

        // Parse status code
        let status_code: u16 = status_line
            .split_whitespace()
            .nth(1)
            .and_then(|s| s.parse().ok())
            .unwrap_or(0);

        // Read headers
        let mut headers: StdHashMap<String, String> = StdHashMap::new();
        loop {
            let mut line = String::new();
            reader
                .read_line(&mut line)
                .map_err(|e| format!("net_http: read headers: {e}"))?;
            let trimmed = line.trim_end();
            if trimmed.is_empty() {
                break;
            }
            if let Some(colon) = trimmed.find(':') {
                let key = trimmed[..colon].trim().to_lowercase();
                let val = trimmed[colon + 1..].trim().to_string();
                headers.insert(key, val);
            }
        }

        // Handle redirects (301, 302, 303, 307, 308)
        if matches!(status_code, 301 | 302 | 303 | 307 | 308) {
            if let Some(loc) = headers.get("location") {
                current_url = loc.clone();
                continue;
            }
        }

        // Read body
        use std::io::Read;
        let response_body = if let Some(te) = headers.get("transfer-encoding") {
            if te.eq_ignore_ascii_case("chunked") {
                // Decode chunked transfer encoding
                let mut body_buf = Vec::new();
                loop {
                    let mut size_line = String::new();
                    reader
                        .read_line(&mut size_line)
                        .map_err(|e| format!("net_http: chunked size: {e}"))?;
                    let chunk_size = usize::from_str_radix(size_line.trim(), 16)
                        .map_err(|_| format!("net_http: bad chunk size: {size_line}"))?;
                    if chunk_size == 0 {
                        break;
                    }
                    let mut chunk = vec![0u8; chunk_size];
                    reader
                        .read_exact(&mut chunk)
                        .map_err(|e| format!("net_http: chunked read: {e}"))?;
                    body_buf.extend_from_slice(&chunk);
                    // consume trailing CRLF
                    let mut crlf = [0u8; 2];
                    let _ = reader.read_exact(&mut crlf);
                }
                String::from_utf8_lossy(&body_buf).into_owned()
            } else {
                let mut body_buf = String::new();
                reader
                    .read_to_string(&mut body_buf)
                    .map_err(|e| format!("net_http: read body: {e}"))?;
                body_buf
            }
        } else if let Some(cl) = headers.get("content-length") {
            let len: usize = cl
                .parse()
                .map_err(|_| format!("net_http: bad content-length: {cl}"))?;
            let mut body_buf = vec![0u8; len];
            reader
                .read_exact(&mut body_buf)
                .map_err(|e| format!("net_http: read body: {e}"))?;
            String::from_utf8_lossy(&body_buf).into_owned()
        } else {
            let mut body_buf = String::new();
            reader
                .read_to_string(&mut body_buf)
                .map_err(|e| format!("net_http: read body: {e}"))?;
            body_buf
        };

        return Ok(response_body);
    }
    Err(format!("net_http: too many redirects for {url}"))
}

// ── Result / Option variant helpers ──────────────────────────────────────────

/// Construct a `.ok(value)` struct on the builtin heap.
fn mk_ok(inner: Value) -> Value {
    thread_local! {
        static OK_HEAP: std::cell::UnsafeCell<crate::gc::GcHeap> =
            std::cell::UnsafeCell::new(crate::gc::GcHeap::new());
    }
    OK_HEAP.with(|h| {
        let heap = unsafe { &mut *h.get() };
        Value::new_struct(heap, "ok", vec![("value".to_string(), inner)])
    })
}

/// Construct a `.error(message)` struct on the builtin heap.
fn mk_error(msg: impl Into<String>) -> Value {
    thread_local! {
        static ERR_HEAP: std::cell::UnsafeCell<crate::gc::GcHeap> =
            std::cell::UnsafeCell::new(crate::gc::GcHeap::new());
    }
    ERR_HEAP.with(|h| {
        let heap = unsafe { &mut *h.get() };
        Value::new_struct(heap, "error", vec![("value".to_string(), mk_str(msg))])
    })
}
