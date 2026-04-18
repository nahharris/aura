use crate::ast::{
    Arm, BinaryOp, Decl, Expr, FunctionDecl, LabeledClosureArg, MacroDecl, Param, Pattern, Program,
    StaticArg, StaticParam, StaticParamKind, StaticValueExpr, TypeExpr, UseDecl,
};
use crate::lexer::lex_with_comments;
use crate::token::TokenKind;
use crate::Parser;

pub struct FormatOptions {
    pub indent_width: usize,
    pub max_width: usize,
}

impl Default for FormatOptions {
    fn default() -> Self {
        Self {
            indent_width: 4,
            max_width: 100,
        }
    }
}

pub fn format_source(source: &str, options: &FormatOptions) -> String {
    let parsed = match Parser::parse_source(source) {
        Ok(program) => program,
        Err(_) => return source.to_string(),
    };
    let comments = extract_comments(source);

    let mut f = Formatter::new(options);
    f.format_program(&parsed);
    let rendered = f.finish(source.ends_with('\n'));
    inject_comments(&rendered, &comments, source.ends_with('\n'))
}

#[derive(Debug, Clone)]
struct CommentToken {
    line: usize,
    column: usize,
    text: String,
    is_inline: bool,
}

fn extract_comments(source: &str) -> Vec<CommentToken> {
    let Ok(tokens) = lex_with_comments(source) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for token in tokens {
        match token.kind {
            TokenKind::LineComment(text) | TokenKind::BlockComment(text) => {
                out.push(CommentToken {
                    line: token.span.line,
                    column: token.span.column,
                    is_inline: token.span.column > 1,
                    text,
                });
            }
            _ => {}
        }
    }
    out
}

fn inject_comments(formatted: &str, comments: &[CommentToken], trailing_newline: bool) -> String {
    if comments.is_empty() {
        return formatted.to_string();
    }

    let mut lines: Vec<String> = formatted.lines().map(|l| l.to_string()).collect();
    let mut inserted = 0usize;

    for comment in comments {
        let mut line_idx = comment.line.saturating_sub(1) + inserted;
        if line_idx > lines.len() {
            line_idx = lines.len();
        }

        if comment.is_inline {
            if line_idx >= lines.len() {
                lines.push(comment.text.clone());
                continue;
            }
            let line = &mut lines[line_idx];
            let trimmed = line.trim_end();
            if trimmed.ends_with('}') && !trimmed.ends_with("};") {
                if let Some(pos) = line.rfind('}') {
                    line.replace_range(pos..=pos, "};");
                }
            }
            let visual_len = line.chars().count();
            let desired_col = comment.column.saturating_sub(1);
            if desired_col > visual_len {
                line.push_str(&" ".repeat(desired_col - visual_len));
            } else if !line.ends_with(' ') {
                line.push(' ');
            }
            line.push_str(&comment.text);
        } else {
            let mut text_lines = comment.text.lines();
            if let Some(first) = text_lines.next() {
                let first_line = if comment.column > 1 {
                    format!("{}{}", " ".repeat(comment.column - 1), first)
                } else {
                    first.to_string()
                };
                lines.insert(line_idx, first_line);
                inserted += 1;
                line_idx += 1;
            }
            for rest in text_lines {
                lines.insert(line_idx, rest.to_string());
                inserted += 1;
                line_idx += 1;
            }
        }
    }

    let mut out = lines.join("\n");
    if trailing_newline {
        out.push('\n');
    }
    out
}

pub fn unified_diff(old: &str, new: &str, path: &str) -> String {
    if old == new {
        return String::new();
    }

    let mut out = String::new();
    out.push_str(&format!("--- {path}\n"));
    out.push_str(&format!("+++ {path}\n"));

    let old_lines: Vec<&str> = old.lines().collect();
    let new_lines: Vec<&str> = new.lines().collect();
    let max = old_lines.len().max(new_lines.len());

    for i in 0..max {
        match (old_lines.get(i), new_lines.get(i)) {
            (Some(a), Some(b)) if a == b => out.push_str(&format!(" {}\n", a)),
            (Some(a), Some(b)) => {
                out.push_str(&format!("-{}\n", a));
                out.push_str(&format!("+{}\n", b));
            }
            (Some(a), None) => out.push_str(&format!("-{}\n", a)),
            (None, Some(b)) => out.push_str(&format!("+{}\n", b)),
            (None, None) => {}
        }
    }

    out
}

struct Formatter<'a> {
    options: &'a FormatOptions,
    out: String,
    indent: usize,
}

impl<'a> Formatter<'a> {
    fn new(options: &'a FormatOptions) -> Self {
        Self {
            options,
            out: String::new(),
            indent: 0,
        }
    }

    fn finish(mut self, trailing_newline: bool) -> String {
        while self.out.ends_with('\n') {
            self.out.pop();
        }
        if trailing_newline {
            self.out.push('\n');
        }
        self.out
    }

    fn format_program(&mut self, program: &Program) {
        for (i, decl) in program.declarations.iter().enumerate() {
            self.write_decl(decl);
            if i + 1 < program.declarations.len() {
                self.newline();
            }
            self.newline();
        }
    }

    fn write_decl(&mut self, decl: &Decl) {
        match decl {
            Decl::Assign {
                name, value, doc, ..
            } => {
                self.write_indent();
                if let Some(doc) = doc {
                    self.write_doc_prefix(&doc.markdown);
                    self.out.push(' ');
                }
                self.out.push_str("def ");
                self.out.push_str(name);
                self.out.push_str(" = ");
                self.write_expr(value, false);
                self.out.push(';');
            }
            Decl::Function(fun) => self.write_function(fun),
            Decl::Macro(mac) => self.write_macro(mac),
            Decl::Use(use_decl) => self.write_use(use_decl),
        }
    }

    fn write_use(&mut self, use_decl: &UseDecl) {
        self.write_indent();
        self.out.push_str("use ");
        self.out.push_str(&use_decl.target);
        self.out.push(';');
    }

    fn write_function(&mut self, fun: &FunctionDecl) {
        self.write_indent();
        if let Some(doc) = &fun.doc {
            self.write_doc_prefix(&doc.markdown);
            self.out.push(' ');
        }
        self.out.push_str("def");
        self.write_static_params(&fun.static_params);
        self.out.push(' ');
        if let Some(receiver) = &fun.receiver {
            self.write_type_expr(receiver);
            self.out.push('.');
        }
        self.out.push_str(&fun.name);
        self.write_params(&fun.params);
        self.out.push_str(" -> ");
        self.write_type_expr(&fun.return_type);
        self.out.push(' ');
        self.write_block_expr(&fun.body, false);
    }

    fn write_macro(&mut self, mac: &MacroDecl) {
        self.write_indent();
        self.out.push_str("defmacro");
        self.write_static_params(&mac.static_params);
        self.out.push(' ');
        self.out.push_str(&mac.name);
        self.write_params(&mac.params);
        self.out.push_str(" -> ");
        self.write_type_expr(&mac.return_type);
        self.out.push(' ');
        self.write_block_expr(&mac.body, false);
    }

    fn write_static_params(&mut self, params: &[StaticParam]) {
        if params.is_empty() {
            return;
        }
        self.out.push('[');
        for (i, param) in params.iter().enumerate() {
            if i > 0 {
                self.out.push_str(", ");
            }
            self.out.push_str(&param.name);
            if let StaticParamKind::Constraint(ty) = &param.kind {
                self.out.push_str(": ");
                self.write_type_expr(ty);
            }
        }
        self.out.push(']');
    }

    fn write_doc_prefix(&mut self, markdown: &str) {
        self.out.push_str("doc[");
        self.out.push('"');
        self.out.push_str(&escape_string_literal(markdown));
        self.out.push('"');
        self.out.push(']');
    }

    fn write_params(&mut self, params: &[Param]) {
        self.out.push('(');
        for (i, p) in params.iter().enumerate() {
            if i > 0 {
                self.out.push_str(", ");
            }
            self.out.push_str(&p.name);
            self.out.push_str(": ");
            self.write_type_expr(&p.ty);
        }
        self.out.push(')');
    }

    fn write_expr(&mut self, expr: &Expr, parenthesize: bool) {
        let expr = expr.unspanned();
        if parenthesize {
            self.out.push('(');
        }

        match expr {
            Expr::Ident(v) | Expr::Int(v) | Expr::Float(v) | Expr::String(v) | Expr::Char(v) => {
                self.out.push_str(v)
            }
            Expr::DotIdent { name, payload } => {
                self.out.push('.');
                self.out.push_str(name);
                if let Some(payload) = payload {
                    self.out.push('(');
                    self.write_expr(payload, false);
                    self.out.push(')');
                }
            }
            Expr::Tuple(items) => {
                self.out.push('(');
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        self.out.push_str(", ");
                    }
                    self.write_expr(item, false);
                }
                self.out.push(')');
            }
            Expr::Struct(fields) => {
                self.out.push('(');
                for (i, (name, value)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.out.push_str(", ");
                    }
                    self.out.push_str(name);
                    self.out.push_str(" = ");
                    self.write_expr(value, false);
                }
                self.out.push(')');
            }
            Expr::Block(items) => self.write_inline_block(items),
            Expr::List(items) => {
                self.out.push('[');
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        self.out.push_str(", ");
                    }
                    self.write_expr(item, false);
                }
                self.out.push(']');
            }
            Expr::Dict(entries) => {
                self.out.push('[');
                for (i, (k, v)) in entries.iter().enumerate() {
                    if i > 0 {
                        self.out.push_str(", ");
                    }
                    self.write_expr(k, false);
                    self.out.push_str(" = ");
                    self.write_expr(v, false);
                }
                self.out.push(']');
            }
            Expr::Closure {
                params,
                return_type,
            } => {
                self.out.push('{');
                if !params.is_empty() || return_type.is_some() {
                    self.out.push(' ');
                    for (i, p) in params.iter().enumerate() {
                        if i > 0 {
                            self.out.push_str(", ");
                        }
                        self.out.push_str(&p.name);
                        self.out.push_str(": ");
                        self.write_type_expr(&p.ty);
                    }
                    if let Some(ret) = return_type {
                        if !params.is_empty() {
                            self.out.push(' ');
                        }
                        self.out.push_str("-> ");
                        self.write_type_expr(ret);
                    }
                    self.out.push(' ');
                }
                self.out.push('}');
            }
            Expr::Placeholder => self.out.push('_'),
            Expr::MultiArm(arms) => self.write_multi_arm(arms),
            Expr::Call {
                callee,
                static_args,
                args,
                trailing,
            } => self.write_call(callee, static_args, args, trailing),
            Expr::Member { object, field } => {
                self.write_expr(object, false);
                self.out.push('.');
                self.out.push_str(field);
            }
            Expr::MacroApply {
                macro_name,
                static_args,
                operand,
            } => {
                self.out.push_str(macro_name);
                self.write_static_args(static_args);
                self.out.push(' ');
                self.write_expr(operand, true);
            }
            Expr::Binary { op, lhs, rhs } => self.write_binary(*op, lhs, rhs),
            Expr::TypeExpr(ty) => self.write_type_expr(ty),
            Expr::Label { label, expr } => {
                self.out.push_str(".[");
                self.out.push('.');
                self.out.push_str(label);
                self.out.push(']');
                self.out.push(' ');
                self.write_expr(expr, true);
            }
            Expr::Cast { expr, ty } => {
                self.write_expr(expr, false);
                self.out.push_str(": ");
                self.write_type_expr(ty);
            }
            Expr::Spanned { .. } => unreachable!(),
        }

        if parenthesize {
            self.out.push(')');
        }
    }

    fn write_call(
        &mut self,
        callee: &Expr,
        static_args: &[StaticArg],
        args: &[Expr],
        trailing: &[LabeledClosureArg],
    ) {
        self.write_expr(callee, false);
        self.write_static_args(static_args);
        if !args.is_empty() || trailing.is_empty() {
            self.out.push('(');
            for (i, arg) in args.iter().enumerate() {
                if i > 0 {
                    self.out.push_str(", ");
                }
                self.write_expr(arg, false);
            }
            self.out.push(')');
        }

        if trailing.is_empty() {
            return;
        }

        for t in trailing {
            self.out.push(' ');
            self.out.push_str(&t.label);
            self.out.push(' ');
            self.write_block_expr(&t.body, true);
        }
    }

    fn write_multi_arm(&mut self, arms: &[Arm]) {
        self.out.push('{');
        if arms.is_empty() {
            self.out.push('}');
            return;
        }
        self.newline();
        self.indent += 1;
        for arm in arms {
            self.write_indent();
            self.write_arm(arm);
            self.out.push(',');
            self.newline();
        }
        self.indent = self.indent.saturating_sub(1);
        self.write_indent();
        self.out.push('}');
    }

    fn write_arm(&mut self, arm: &Arm) {
        if !arm.patterns.is_empty() {
            for (i, p) in arm.patterns.iter().enumerate() {
                if i > 0 {
                    self.out.push_str(", ");
                }
                self.write_pattern(p);
            }
            self.out.push(' ');
        }
        if let Some(guard) = &arm.guard {
            self.out.push_str("~ ");
            self.write_expr(guard, false);
            self.out.push(' ');
        }
        self.out.push_str("-> ");
        self.write_expr(&arm.body, false);
    }

    fn write_pattern(&mut self, pattern: &Pattern) {
        match pattern {
            Pattern::Wildcard => self.out.push('_'),
            Pattern::Ident(name) => self.out.push_str(name),
            Pattern::DotVariant { name, payload } => {
                self.out.push('.');
                self.out.push_str(name);
                if let Some(payload) = payload {
                    self.out.push('(');
                    self.write_pattern(payload);
                    self.out.push(')');
                }
            }
        }
    }

    fn write_static_args(&mut self, static_args: &[StaticArg]) {
        if static_args.is_empty() {
            return;
        }
        self.out.push('[');
        for (i, arg) in static_args.iter().enumerate() {
            if i > 0 {
                self.out.push_str(", ");
            }
            match arg {
                StaticArg::Type(ty) => self.write_type_expr(ty),
                StaticArg::Value(v) => self.write_static_value(v),
            }
        }
        self.out.push(']');
    }

    fn write_static_value(&mut self, v: &StaticValueExpr) {
        match v {
            StaticValueExpr::Int(s)
            | StaticValueExpr::Float(s)
            | StaticValueExpr::Ident(s)
            | StaticValueExpr::String(s)
            | StaticValueExpr::Char(s) => self.out.push_str(s),
        }
    }

    fn write_type_expr(&mut self, ty: &TypeExpr) {
        match ty {
            TypeExpr::Named { name, args } => {
                self.out.push_str(name);
                self.write_static_args(args);
            }
            TypeExpr::Tuple(items) => {
                self.out.push('(');
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        self.out.push_str(", ");
                    }
                    self.write_type_expr(item);
                }
                self.out.push(')');
            }
            TypeExpr::Struct(fields) => {
                self.out.push('(');
                for (i, (name, ty)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.out.push_str(", ");
                    }
                    self.out.push_str(name);
                    self.out.push_str(": ");
                    self.write_type_expr(ty);
                }
                self.out.push(')');
            }
            TypeExpr::Static(inner) => {
                self.out.push_str("static ");
                self.write_type_expr(inner);
            }
            TypeExpr::InferHole => self.out.push('_'),
        }
    }

    fn write_binary(&mut self, op: BinaryOp, lhs: &Expr, rhs: &Expr) {
        let op_text = op_text(op);
        let left = expr_to_inline(lhs);
        let right = expr_to_inline(rhs);
        let inline = format!("{left} {op_text} {right}");
        if inline.chars().count() <= self.options.max_width {
            self.out.push_str(&inline);
            return;
        }

        self.out.push_str(&left);
        self.newline();
        self.write_indent();
        self.out.push_str(op_text);
        self.out.push(' ');
        self.out.push_str(&right);
    }

    fn write_block_expr(&mut self, body: &Expr, compact: bool) {
        let body = body.unspanned();
        match body {
            Expr::MultiArm(arms) => self.write_multi_arm(arms),
            Expr::Block(items) => self.write_sequence_block(items, compact),
            _ => {
                self.out.push('{');
                if compact {
                    self.out.push(' ');
                    self.write_expr(body, false);
                    self.out.push(' ');
                    self.out.push('}');
                } else {
                    self.newline();
                    self.indent += 1;
                    self.write_indent();
                    self.write_expr(body, false);
                    self.out.push(';');
                    self.newline();
                    self.indent = self.indent.saturating_sub(1);
                    self.write_indent();
                    self.out.push('}');
                }
            }
        }
    }

    fn write_inline_block(&mut self, items: &[Expr]) {
        if items.is_empty() {
            self.out.push_str("{}");
            return;
        }

        if items.len() == 1 {
            self.out.push('{');
            self.out.push(' ');
            self.write_expr(&items[0], false);
            self.out.push(' ');
            self.out.push('}');
            return;
        }

        self.write_sequence_block(items, false);
    }

    fn write_sequence_block(&mut self, items: &[Expr], compact: bool) {
        self.out.push('{');
        if items.is_empty() {
            if compact {
                self.out.push(' ');
            }
            self.out.push('}');
            return;
        }

        if compact && items.len() == 1 {
            self.out.push(' ');
            self.write_expr(&items[0], false);
            self.out.push(' ');
            self.out.push('}');
            return;
        }

        self.newline();
        self.indent += 1;
        for (idx, item) in items.iter().enumerate() {
            self.write_indent();
            self.write_expr(item, false);
            if idx + 1 < items.len() {
                self.out.push(';');
            }
            self.newline();
        }
        self.indent = self.indent.saturating_sub(1);
        self.write_indent();
        self.out.push('}');
    }

    fn write_indent(&mut self) {
        self.out
            .push_str(&" ".repeat(self.indent * self.options.indent_width));
    }

    fn newline(&mut self) {
        if !self.out.ends_with('\n') {
            self.out.push('\n');
        }
    }
}

fn op_text(op: BinaryOp) -> &'static str {
    match op {
        BinaryOp::Elvis => "?:",
        BinaryOp::Or => "||",
        BinaryOp::And => "&&",
        BinaryOp::Eq => "==",
        BinaryOp::Neq => "!=",
        BinaryOp::Lt => "<",
        BinaryOp::Le => "<=",
        BinaryOp::Gt => ">",
        BinaryOp::Ge => ">=",
        BinaryOp::Range => "..",
        BinaryOp::Pipe => "|>",
        BinaryOp::Add => "+",
        BinaryOp::Sub => "-",
        BinaryOp::Mul => "*",
        BinaryOp::Div => "/",
        BinaryOp::Mod => "%",
        BinaryOp::Colon => ":",
    }
}

fn expr_to_inline(expr: &Expr) -> String {
    let e = expr.unspanned();
    match e {
        Expr::Ident(v) | Expr::Int(v) | Expr::Float(v) | Expr::String(v) | Expr::Char(v) => {
            v.clone()
        }
        Expr::Member { object, field } => format!("{}.{}", expr_to_inline(object), field),
        _ => "<expr>".to_string(),
    }
}

fn escape_string_literal(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            _ => out.push(ch),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::{format_source, FormatOptions};

    #[test]
    fn preserves_trailing_closure_continuation_on_same_line() {
        let src = "def x = do_stuff(1) task { print(1) } finally { print(2) }\n";
        let out = format_source(src, &FormatOptions::default());
        assert!(out.contains("} finally {"));
    }

    #[test]
    fn inserts_commas_between_cases_arms() {
        let src = "def label = cases when {\n~ 10.0 > 2.0 -> 42,\n-> 0,\n}\n";
        let out = format_source(src, &FormatOptions::default());
        assert!(out.contains("~ 10.0 > 2.0 -> 42,"));
        assert!(out.contains("-> 0,"));
    }

    #[test]
    fn keeps_comments_text() {
        let src = "def x = 1 // trailing\n// full line\n";
        let out = format_source(src, &FormatOptions::default());
        assert!(out.contains("// trailing"));
        assert!(out.contains("// full line"));
    }

    #[test]
    fn inline_comment_after_brace_gets_semicolon_before_comment() {
        let src = "def x = if(true) then { 1 } else { 2 } // comment\n";
        let out = format_source(src, &FormatOptions::default());
        assert!(out.contains("}; // comment"));
    }

    #[test]
    fn inline_comment_respects_original_column_when_possible() {
        let src = "def x = 1        // aligned\n";
        let out = format_source(src, &FormatOptions::default());
        let line = out.lines().next().unwrap_or_default();
        let col = line.find("// aligned").unwrap_or(0) + 1;
        assert!(col >= 17);
    }

    #[test]
    fn formats_pipe_operator_expression() {
        let src = "def x = a |> b\n";
        let out = format_source(src, &FormatOptions::default());
        assert!(out.contains("a |> b"));
    }

    #[test]
    fn formats_placeholder_in_call_arguments() {
        let src = "def x = f(5, _)\n";
        let out = format_source(src, &FormatOptions::default());
        assert!(out.contains("f(5, _)"));
    }
}
