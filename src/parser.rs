use pest::{iterators::Pair, iterators::Pairs, Parser};
use pest::pratt_parser::{Assoc, Op, PrattParser};
use crate::ast::*;
use crate::{AuraError, AuraResult};

#[derive(pest_derive::Parser)]
#[grammar = "grammar.pest"]
pub struct AuraParser;

lazy_static::lazy_static! {
    static ref PRATT_PARSER: PrattParser<Rule> = {
        use Rule::*;
        PrattParser::new()
            .op(Op::infix(infix, Assoc::Left))
            .op(Op::prefix(prefix))
            .op(Op::postfix(postfix))
    };
}

pub fn parse(input: &str) -> AuraResult<Vec<Stmt>> {
    let mut pairs = AuraParser::parse(Rule::program, input)?;
    let mut stmts = Vec::new();
    if let Some(program) = pairs.next() {
        for pair in program.into_inner() {
            match pair.as_rule() {
                Rule::stmt => stmts.push(parse_stmt(pair)?),
                Rule::EOI => (),
                _ => unreachable!(),
            }
        }
    }
    Ok(stmts)
}

fn parse_stmt(pair: Pair<Rule>) -> AuraResult<Stmt> {
    let inner = pair.into_inner().next().unwrap();
    match inner.as_rule() {
        Rule::decl => parse_decl(inner),
        Rule::expr_stmt => {
            let expr_pair = inner.into_inner().next().unwrap();
            let expr = parse_expr(expr_pair)?;
            Ok(Stmt::Expr(expr))
        }
        _ => unreachable!(),
    }
}

fn parse_decl(pair: Pair<Rule>) -> AuraResult<Stmt> {
    let inner = pair.into_inner().next().unwrap();
    match inner.as_rule() {
        Rule::let_decl => {
            let assignments = parse_assignments(inner.into_inner().next().unwrap())?;
            Ok(Stmt::Let { assignments })
        },
        Rule::const_decl => {
            let assignments = parse_assignments(inner.into_inner().next().unwrap())?;
            Ok(Stmt::Const { assignments })
        },
        Rule::fn_decl => parse_fn_decl(inner),
        _ => Ok(Stmt::Expr(Expr::Literal(Literal::Null))),
    }
}

fn parse_assignments(pair: Pair<Rule>) -> AuraResult<Vec<(String, Expr)>> {
    let mut assigns = Vec::new();
    for p in pair.into_inner() {
        let mut inner = p.into_inner();
        let ident = inner.next().unwrap().as_str().to_string();
        let expr = parse_expr(inner.next().unwrap())?;
        assigns.push((ident, expr));
    }
    Ok(assigns)
}

fn parse_fn_decl(pair: Pair<Rule>) -> AuraResult<Stmt> {
    let mut inner = pair.into_inner();
    let name_pair = inner.next().unwrap(); // fn_name
    let name = name_pair.as_str().to_string();
    
    let sig_pair = inner.next().unwrap(); // fn_signature
    let params = parse_fn_params(sig_pair)?;
    
    let body_pair = inner.next().unwrap();
    let body = if body_pair.as_rule() == Rule::block {
        parse_block(body_pair)?
    } else {
        Block { stmts: vec![], final_expr: None }
    };

    Ok(Stmt::Fn(FnDecl {
        name,
        params,
        return_type: None, // TODO: Parse return type
        body,
    }))
}

fn parse_fn_params(pair: Pair<Rule>) -> AuraResult<Vec<Param>> {
    let mut params = Vec::new();
    if let Some(inner) = pair.into_inner().next() { // param_list
        for param_pair in inner.into_inner() {
            // param = { (identifier ~ identifier) | (identifier ~ ":" ~ type_expr) | identifier }
            let inner_param = param_pair.into_inner();
            // Simplify: just take the first identifier as name for now, ignore type/label details for prototype
            // Wait, `identifier ~ identifier` is `label name`.
            // `identifier ~ : ~ type` is `name : type`.
            // `identifier` is `name`.
            let tokens: Vec<_> = inner_param.collect();
            let name = if tokens.len() == 2 && tokens[1].as_rule() == Rule::identifier {
                tokens[1].as_str().to_string() // Second ident is name
            } else {
                tokens[0].as_str().to_string() // First is name
            };
            
            params.push(Param { name, label: None, ty: None });
        }
    }
    Ok(params)
}

fn parse_block(pair: Pair<Rule>) -> AuraResult<Block> {
    let mut inner = pair.into_inner();
    let mut next = inner.peek();
    if let Some(n) = next {
        if n.as_rule() == Rule::closure_params {
            inner.next(); // Skip closure params for now
        }
    }
    
    let body_inner = inner.next().unwrap().into_inner();
    let mut stmts = Vec::new();
    let mut final_expr = None;

    for p in body_inner {
        match p.as_rule() {
            Rule::stmt => stmts.push(parse_stmt(p)?),
            Rule::expr => final_expr = Some(Box::new(parse_expr(p)?)),
            _ => (),
        }
    }

    Ok(Block { stmts, final_expr })
}

fn parse_expr(pair: Pair<Rule>) -> AuraResult<Expr> {
    let pairs = pair.into_inner();
    PRATT_PARSER
        .map_primary(|primary| parse_primary(primary))
        .map_prefix(|op, rhs| {
            let rhs = rhs?;
            let op = match op.as_str() {
                "-" => UnaryOp::Neg,
                "!" => UnaryOp::Not,
                _ => unreachable!(),
            };
            Ok(Expr::UnaryOp { op, expr: Box::new(rhs) })
        })
        .map_postfix(|lhs, op| {
            let lhs = lhs?;
            match op.as_rule() {
                Rule::postfix => {
                    let inner = op.into_inner().next().unwrap();
                    match inner.as_rule() {
                        Rule::call_args => {
                            let args = parse_args(inner)?;
                            Ok(combine_call(lhs, args, None))
                        },
                        Rule::trailing_lambda => {
                            let tl = parse_trailing_lambda(inner)?;
                            Ok(combine_call(lhs, vec![], Some(tl)))
                        },
                        Rule::method_call => {
                            let method = inner.into_inner().next().unwrap().as_str();
                            let func = Box::new(Expr::DotIdentifier(format!(".{}", method)));
                            Ok(combine_call(func.as_ref().clone(), vec![Argument { label: None, value: lhs }], None))
                        },
                        Rule::safe_nav => {
                            let method = inner.into_inner().next().unwrap().as_str();
                            let func = Box::new(Expr::DotIdentifier(format!("?.{}", method)));
                            Ok(combine_call(func.as_ref().clone(), vec![Argument { label: None, value: lhs }], None))
                        },
                         _ => Ok(lhs),
                    }
                },
                 _ => unreachable!(),
            }
        })
        .map_infix(|lhs, op, rhs| {
            let lhs = lhs?;
            let rhs = rhs?;
            let op = match op.as_str() {
                "+" => BinaryOp::Add,
                "-" => BinaryOp::Sub,
                "*" => BinaryOp::Mul,
                "/" => BinaryOp::Div,
                "==" => BinaryOp::Eq,
                "!=" => BinaryOp::Neq,
                "<" => BinaryOp::Lt,
                ">" => BinaryOp::Gt,
                "<=" => BinaryOp::Le,
                ">=" => BinaryOp::Ge,
                "&&" => BinaryOp::And,
                "||" => BinaryOp::Or,
                "=" => BinaryOp::Assign,
                _ => unreachable!(),
            };
            Ok(Expr::BinaryOp { lhs: Box::new(lhs), op, rhs: Box::new(rhs) })
        })
        .parse(pairs)
        .map(|e| e.optimize())
}

fn parse_primary(pair: Pair<Rule>) -> AuraResult<Expr> {
    let inner = pair.into_inner().next().unwrap();
    match inner.as_rule() {
        Rule::literal => parse_literal(inner),
        Rule::identifier => Ok(Expr::Identifier(inner.as_str().to_string())),
        Rule::block => Ok(Expr::Block(parse_block(inner)?)),
        Rule::list_literal => {
            let items = parse_list_items(inner)?;
            Ok(Expr::List(items))
        },
        Rule::tuple_literal => {
            let items = parse_list_items(inner)?;
            Ok(Expr::Tuple(items))
        },
        Rule::dot_identifier => Ok(Expr::DotIdentifier(inner.as_str().to_string())),
        _ => unreachable!("Unexpected primary: {:?}", inner.as_rule()),
    }
}

fn parse_list_items(pair: Pair<Rule>) -> AuraResult<Vec<Expr>> {
    // pair is list_literal or tuple_literal. 
    // list_literal = { "[" ~ list_items? ~ "]" }
    // The pair passed here is the INNER of list_literal (which is list_items?)
    // No, parse_primary calls: `parse_list_items(inner)`. 
    // `inner` is `list_literal`.
    // `list_literal` inner is `list_items`.
    
    let mut items = Vec::new();
    if let Some(list_items_pair) = pair.into_inner().next() {
        // list_items = { list_item ~ ("," ~ list_item)* ~ ","? }
        for item_pair in list_items_pair.into_inner() {
            // item_pair is list_item
            // list_item = { (decl | (expr ~ ";"))* ~ expr }
            let mut stmts = Vec::new();
            let mut final_expr = None;
            
            let inner_rules: Vec<_> = item_pair.into_inner().collect();
            let len = inner_rules.len();
            
            if len > 0 {
                for (i, p) in inner_rules.iter().enumerate() {
                    if i == len - 1 {
                        // The last element is the expression value
                        final_expr = Some(Box::new(parse_expr(p.clone())?));
                    } else {
                        // Preceding elements are statements
                        if p.as_rule() == Rule::decl {
                             stmts.push(parse_decl(p.clone())?);
                        } else if p.as_rule() == Rule::expr {
                             stmts.push(Stmt::Expr(parse_expr(p.clone())?));
                        }
                    }
                }
            }
            
            if stmts.is_empty() {
                if let Some(e) = final_expr {
                    items.push(*e);
                }
            } else {
                items.push(Expr::Block(Block { stmts, final_expr }));
            }
        }
    }
    Ok(items)
}

fn parse_literal(pair: Pair<Rule>) -> AuraResult<Expr> {
    let inner = pair.into_inner().next().unwrap();
    match inner.as_rule() {
        Rule::int => Ok(Expr::Literal(Literal::Int(inner.as_str().parse().unwrap()))),
        Rule::float => Ok(Expr::Literal(Literal::Float(inner.as_str().parse().unwrap()))),
        Rule::string => Ok(Expr::Literal(Literal::String(inner.as_str().trim_matches('"').to_string()))),
        Rule::bool => Ok(Expr::Literal(Literal::Bool(inner.as_str() == "true"))),
        Rule::null => Ok(Expr::Literal(Literal::Null)),
        _ => unreachable!(),
    }
}

fn parse_args(pair: Pair<Rule>) -> AuraResult<Vec<Argument>> {
    let mut args = Vec::new();
    if let Some(inner) = pair.into_inner().next() {
        for arg_pair in inner.into_inner() {
             let mut arg_inner = arg_pair.into_inner();
             let first = arg_inner.next().unwrap();
             let (label, expr_pair) = if first.as_rule() == Rule::identifier {
                 (Some(first.as_str().to_string()), arg_inner.next().unwrap())
             } else {
                 (None, first)
             };
             args.push(Argument { label, value: parse_expr(expr_pair)? });
        }
    }
    Ok(args)
}

fn parse_trailing_lambda(pair: Pair<Rule>) -> AuraResult<TrailingLambda> {
    let mut inner = pair.into_inner();
    let first = inner.next().unwrap();
    let (label, block_pair) = if first.as_rule() == Rule::identifier {
        (Some(first.as_str().to_string()), inner.next().unwrap())
    } else {
        (None, first)
    };
    Ok(TrailingLambda { label, lambda: parse_block(block_pair)? })
}

fn combine_call(lhs: Expr, mut new_args: Vec<Argument>, new_trailing: Option<TrailingLambda>) -> Expr {
    let mut func = Box::new(lhs);
    let mut args = Vec::new();
    let mut trailing = Vec::new();
    
    if let Expr::Call { func: f, args: a, trailing: t } = *func.clone() {
         if new_args.is_empty() && new_trailing.is_some() {
             let mut t = t;
             t.push(new_trailing.unwrap());
             return Expr::Call {
                 func: f,
                 args: a,
                 trailing: t
             };
         }
    }
    
    if !new_args.is_empty() {
        args = new_args;
    }
    if let Some(tl) = new_trailing {
        trailing.push(tl);
    }
    
    Expr::Call {
        func,
        args,
        trailing
    }
}

impl Expr {
    fn optimize(self) -> Expr {
        match self {
            Expr::Call { func, args, trailing } => {
                if let Expr::Identifier(ref name) = *func {
                    match name.as_str() {
                        "if" => {
                            if args.len() == 1 && !trailing.is_empty() {
                                let cond = Box::new(args[0].value.clone().optimize());
                                let then_block = Box::new(trailing[0].lambda.clone());
                                let else_block = if trailing.len() > 1 {
                                    Some(Box::new(trailing[1].lambda.clone()))
                                } else {
                                    None
                                };
                                return Expr::If { cond, then_block, else_block };
                            }
                        },
                        "while" => {
                             if args.len() == 1 && !trailing.is_empty() {
                                 return Expr::While {
                                     cond: Box::new(args[0].value.clone()),
                                     body: Box::new(trailing[0].lambda.clone())
                                 };
                             }
                        },
                        "loop" => {
                             if args.is_empty() && !trailing.is_empty() {
                                 return Expr::Loop {
                                     body: Box::new(trailing[0].lambda.clone())
                                 };
                             }
                        },
                        _ => {}
                    }
                }
                Expr::Call { func, args, trailing }
            },
            _ => self,
        }
    }
}
