extern crate itertools;
use core::slice::Iter;
use itertools::MultiPeek;
use std::fmt;
use std::error;
use crate::tokenizer::{Keyword, Token, TokNLoc};

#[derive(Debug)]
pub enum BinaryOp {
    Addition,
    Subtraction,
    Multiplication,
    Division,
    Remainder,
    LogicalAnd,
    LogicalOr,
    Equal,
    NotEqual,
    Less,
    Greater,
    LessEqual,
    GreaterEqual,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    LeftShift,
    RightShift,
}

#[derive(Debug)]
pub enum UnaryOp {
    Negate,
    Not,
    Complement,
}

#[derive(Debug)]
pub enum AssignmentKind {
    Write,
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
    BitwiseXor,
    BitwiseOr,
    BitwiseAnd,
    LeftShift,
    RightShift,
}

#[derive(Debug)]
pub enum FixOp {
    Inc,
    Dec,
}

#[derive(Debug)]
pub enum Expression {
    Assign(AssignmentKind, String, Box<Expression>),
    BinaryOp(BinaryOp, Box<Expression>, Box<Expression>),
    UnaryOp(UnaryOp, Box<Expression>),
    PrefixOp(FixOp, String),
    PostfixOp(FixOp, String),
    Constant(i64),
    Variable(String),
}

#[derive(Debug)]
pub enum Statement {
    Return(Expression),
    Decl(String, Option<Expression>),
    Expr(Expression),
}

#[derive(Debug)]
pub enum Function {
    Func(String, Vec<Statement>),
}

#[derive(Debug)]
pub enum Program {
    Prog(Function),
}

fn print_expression(expr: &Expression, lvl: i32) {
    match expr {
        Expression::Assign(kind, var, exp) => {
            println!("{:<1$}Assign {2:?} {3:?} {{", "", (lvl * 2) as usize, var, kind);
            print_expression(exp, lvl + 1);
            println!("{:<1$}}}", "", (lvl * 2) as usize);
        }
        Expression::BinaryOp(binop, exp1, exp2) => {
            println!("{:<1$}BinaryOp {2:?} {{", "", (lvl * 2) as usize, binop);
            print_expression(exp1, lvl + 1);
            print_expression(exp2, lvl + 1);
            println!("{:<1$}}}", "", (lvl * 2) as usize);
        }
        Expression::UnaryOp(unop, exp) => {
            println!("{:<1$}UnaryOp {2:?} {{", "", (lvl * 2) as usize, unop);
            print_expression(exp, lvl + 1);
            println!("{:<1$}}}", "", (lvl * 2) as usize);
        }
        Expression::PrefixOp(fop, id) => {
            println!("{:<1$}PrefixOp {2:?} {3:?}", "", (lvl * 2) as usize, fop, id);
        }
        Expression::PostfixOp(fop, id) => {
            println!("{:<1$}PrefixOp {2:?} {3:?}", "", (lvl * 2) as usize, id, fop);
        }
        Expression::Variable(id) => {
            println!("{0:<1$}Variable {2}", "", (lvl * 2) as usize, id);
        }
        Expression::Constant(val) => {
            println!("{0:<1$}Constant {2}", "", (lvl * 2) as usize, val);
        }
    }
}

fn print_statement(stmt: &Statement, lvl: i32) {
    match stmt {
        Statement::Return(expr) => {
            println!("{: <1$}Return {{", "", (lvl * 2) as usize);
            print_expression(expr, lvl + 1);
            println!("{: <1$}}}", "", (lvl * 2) as usize);
        }
        Statement::Decl(id, init) => {
            if let Some(expr) = init {
                println!("{: <1$}Decl {2:?} {{", "", (lvl * 2) as usize, id);
                print_expression(expr, lvl + 1);
                println!("{: <1$}}}", "", (lvl * 2) as usize);
            } else {
                println!("{: <1$}Decl {2:?}", "", (lvl * 2) as usize, id);
            }
        }
        Statement::Expr(expr) => {
            println!("{: <1$}Expr {{", "", (lvl * 2) as usize);
            print_expression(expr, lvl + 1);
            println!("{: <1$}}}", "", (lvl * 2) as usize);
        }
    }
}

pub fn print_program(prog: &Program) {
    let lvl = 0;
    println!("Program {{");
    let Program::Prog(Function::Func(name, stmts)) = prog;
    println!("  Function \"{}\" {{", name);
    for stmt in stmts {
        print_statement(stmt, lvl + 2);
    }
    println!("  }}");
    println!("}}");
}

//===================================================================
// Parsing
//===================================================================

#[derive(Debug, Clone)]
pub struct ParseError {
    pub cursor: usize,
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ParseError {}: {}", self.cursor, self.message)
    }
}

impl error::Error for ParseError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }
}

fn parse_postfix_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression, ParseError> {
    let tok = tokiter.next().unwrap();
    match &tok.token {
        Token::Lparen => {
            let subexpr = parse_expression(tokiter)?;
            let tok = &tokiter.next().unwrap();
            match tok.token {
                Token::Rparen => Ok(subexpr),
                _ => Err(ParseError{cursor:tok.location, message:format!("Missing closing parenthesis after expression, got '{}'.", tok.token)})
            }
        },
        Token::Identifier(id) => {
            match tokiter.peek().unwrap().token {
                Token::Increment => {
                    tokiter.next(); // consume
                    Ok(Expression::PostfixOp(FixOp::Inc, id.to_string()))
                }
                Token::Decrement => {
                    tokiter.next(); // consume
                    Ok(Expression::PostfixOp(FixOp::Dec, id.to_string()))
                }
                _ =>  {
                    tokiter.reset_peek();
                    Ok(Expression::Variable(id.to_string()))
                }
            }
        }
        Token::IntLiteral(v) => {
            Ok(Expression::Constant(*v))
        },
        _ => {
            Err(ParseError{cursor:tok.location, message:format!("Invalid postfix expression. Expected int literal, (expr), or identifier possibly with postfix operator, but got '{}'.", tok.token)})
        }
    }
}

fn parse_prefix_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression, ParseError> {
    let tok = tokiter.peek().unwrap();
    match &tok.token {
        Token::Minus => {
            tokiter.next(); // consume
            let operand = parse_prefix_expression(tokiter)?;
            Ok(Expression::UnaryOp(UnaryOp::Negate, Box::new(operand)))
        }
        Token::Not => {
            tokiter.next(); // consume
            let operand = parse_prefix_expression(tokiter)?;
            Ok(Expression::UnaryOp(UnaryOp::Not, Box::new(operand)))
        }
        Token::Complement => {
            tokiter.next(); // consume
            let operand = parse_prefix_expression(tokiter)?;
            Ok(Expression::UnaryOp(UnaryOp::Complement, Box::new(operand)))
        }
        Token::Increment => {
            tokiter.next(); // consume

            let next_loc = tokiter.peek().unwrap().location; // for error message
            tokiter.reset_peek();

            let operand = parse_postfix_expression(tokiter)?;
            if let Expression::Variable(id) = operand {
                Ok(Expression::PrefixOp(FixOp::Inc, id))
            } else {
                Err(ParseError {
                    cursor: next_loc,
                    message: "Invalid prefix expression. Expected variable identifier after prefix increment/decrement".to_string(),
                })
            }
        }
        Token::Decrement => {
            tokiter.next(); // consume

            let next_loc = tokiter.peek().unwrap().location; // for error message
            tokiter.reset_peek();

            let operand = parse_postfix_expression(tokiter)?;
            if let Expression::Variable(id) = operand {
                Ok(Expression::PrefixOp(FixOp::Dec, id))
            } else {
                Err(ParseError {
                    cursor: next_loc,
                    message: "Invalid prefix expression. Expected variable identifier after prefix increment/decrement".to_string(),
                })
            }
        }
        _ => {
            tokiter.reset_peek();
            parse_postfix_expression(tokiter)
        }
    }
}

fn parse_multiplicative_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression, ParseError> {
    let mut factor = parse_prefix_expression(tokiter)?;

    while let Some(tok) = tokiter.peek() {
        let optop = match tok.token {
            Token::Multiplication => Some(BinaryOp::Multiplication),
            Token::Division => Some(BinaryOp::Division),
            Token::Remainder => Some(BinaryOp::Remainder),
            _ => None,
        };
        if let Some(op) = optop {
            tokiter.next(); // consume
            let next_factor = parse_prefix_expression(tokiter)?;
            factor = Expression::BinaryOp(op, Box::new(factor), Box::new(next_factor));
        } else {
            break;
        }
    }
    tokiter.reset_peek();
    Ok(factor)
}

fn parse_additive_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression, ParseError> {
    let mut term = parse_multiplicative_expression(tokiter)?;

    while let Some(tok) = tokiter.peek() {
        let optop = match tok.token {
            Token::Minus => Some(BinaryOp::Subtraction),
            Token::Plus => Some(BinaryOp::Addition),
            _ => None,
        };
        if let Some(op) = optop {
            tokiter.next(); // consume
            let next_term = parse_multiplicative_expression(tokiter)?;
            term = Expression::BinaryOp(op, Box::new(term), Box::new(next_term));
        } else {
            break;
        }
    }
    tokiter.reset_peek();
    Ok(term)
}

fn parse_shift_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression, ParseError> {
    let mut adexpr = parse_additive_expression(tokiter)?;

    while let Some(tok) = tokiter.peek() {
        let optop = match tok.token {
            Token::LeftShift => Some(BinaryOp::LeftShift),
            Token::RightShift => Some(BinaryOp::RightShift),
            _ => None,
        };
        if let Some(op) = optop {
            tokiter.next(); // consume
            let next_adexpr = parse_additive_expression(tokiter)?;
            adexpr = Expression::BinaryOp(op, Box::new(adexpr), Box::new(next_adexpr));
        } else {
            break;
        }
    }
    tokiter.reset_peek();
    Ok(adexpr)
}

fn parse_relational_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression, ParseError> {
    let mut shiftexpr = parse_shift_expression(tokiter)?;

    while let Some(tok) = tokiter.peek() {
        let optop = match tok.token {
            Token::Greater => Some(BinaryOp::Greater),
            Token::Less => Some(BinaryOp::Less),
            Token::GreaterEqual => Some(BinaryOp::GreaterEqual),
            Token::LessEqual => Some(BinaryOp::LessEqual),
            _ => None,
        };
        if let Some(op) = optop {
            tokiter.next(); // consume
            let next_shiftexpr = parse_shift_expression(tokiter)?;
            shiftexpr = Expression::BinaryOp(op, Box::new(shiftexpr), Box::new(next_shiftexpr));
        } else {
            break;
        }
    }

    tokiter.reset_peek();
    Ok(shiftexpr)
}

fn parse_equality_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression, ParseError> {
    let mut relexpr = parse_relational_expression(tokiter)?;

    while let Some(tok) = tokiter.peek() {
        let optop = match tok.token {
            Token::Equal => Some(BinaryOp::Equal),
            Token::NotEqual => Some(BinaryOp::NotEqual),
            _ => None,
        };
        if let Some(op) = optop {
            tokiter.next(); // consume
            let next_relexpr = parse_relational_expression(tokiter)?;
            relexpr = Expression::BinaryOp(op, Box::new(relexpr), Box::new(next_relexpr));
        } else {
            break;
        }
    }
    tokiter.reset_peek();
    Ok(relexpr)
}

fn parse_bitwise_and_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression, ParseError> {
    let mut eqexpr = parse_equality_expression(tokiter)?;

    while let Some(tok) = tokiter.peek() {
        if let Token::BitwiseAnd = tok.token {
            tokiter.next(); // consume
            let next_eqexpr = parse_equality_expression(tokiter)?;
            eqexpr = Expression::BinaryOp(BinaryOp::BitwiseAnd, Box::new(eqexpr), Box::new(next_eqexpr));
        } else {
            break;
        }
    }
    tokiter.reset_peek();
    Ok(eqexpr)
}

fn parse_bitwise_xor_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression, ParseError> {
    let mut bandexpr = parse_bitwise_and_expression(tokiter)?;

    while let Some(tok) = tokiter.peek() {
        if let Token::BitwiseXor = tok.token {
            tokiter.next(); // consume
            let next_bandexpr = parse_bitwise_and_expression(tokiter)?;
            bandexpr = Expression::BinaryOp(BinaryOp::BitwiseXor, Box::new(bandexpr), Box::new(next_bandexpr));
        } else {
            break;
        }
    }
    tokiter.reset_peek();
    Ok(bandexpr)
}

fn parse_bitwise_or_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression, ParseError> {
    let mut bxorexpr = parse_bitwise_xor_expression(tokiter)?;

    while let Some(tok) = tokiter.peek() {
        if let Token::BitwiseOr = tok.token {
            tokiter.next(); // consume
            let next_bxorexpr = parse_bitwise_xor_expression(tokiter)?;
            bxorexpr = Expression::BinaryOp(BinaryOp::BitwiseOr, Box::new(bxorexpr), Box::new(next_bxorexpr));
        } else {
            break;
        }
    }
    tokiter.reset_peek();
    Ok(bxorexpr)
}

fn parse_logical_and_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression, ParseError> {
    let mut borexpr = parse_bitwise_or_expression(tokiter)?;

    while let Some(tok) = tokiter.peek() {
        if let Token::LogicalAnd = tok.token {
            tokiter.next(); // consume
            let next_borexpr = parse_bitwise_or_expression(tokiter)?;
            borexpr = Expression::BinaryOp(BinaryOp::LogicalAnd, Box::new(borexpr), Box::new(next_borexpr));
        } else {
            break;
        }
    }
    tokiter.reset_peek();
    Ok(borexpr)
}

fn parse_logical_or_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression, ParseError> {
    let mut laexpr = parse_logical_and_expression(tokiter)?;

    while let Some(tok) = tokiter.peek() {
        if let Token::LogicalOr = tok.token {
            tokiter.next(); // consume
            let next_laexpr = parse_logical_and_expression(tokiter)?;
            laexpr = Expression::BinaryOp(BinaryOp::LogicalOr, Box::new(laexpr), Box::new(next_laexpr));
        } else {
            break;
        }
    }
    tokiter.reset_peek();
    Ok(laexpr)
}

fn parse_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression, ParseError> {
    if let Token::Identifier(id) = &tokiter.peek().unwrap().token {
        let ass = match tokiter.peek().unwrap().token {
            Token::Assignment => Some(AssignmentKind::Write),
            Token::AdditionAssignment => Some(AssignmentKind::Add),
            Token::SubtractionAssignment => Some(AssignmentKind::Subtract),
            Token::MultiplicationAssignment => Some(AssignmentKind::Multiply),
            Token::DivisionAssignment => Some(AssignmentKind::Divide),
            Token::RemainderAssignment => Some(AssignmentKind::Remainder),
            Token::BitwiseXorAssignment => Some(AssignmentKind::BitwiseXor),
            Token::BitwiseOrAssignment => Some(AssignmentKind::BitwiseOr),
            Token::BitwiseAndAssignment => Some(AssignmentKind::BitwiseAnd),
            Token::LeftShiftAssignment => Some(AssignmentKind::LeftShift),
            Token::RightShiftAssignment => Some(AssignmentKind::RightShift),
            _ => None,
        };

        if let Some(asskind) = ass {
            tokiter.next(); // consume twice
            tokiter.next();
            let expr = parse_expression(tokiter)?;
            return Ok(Expression::Assign(asskind, id.to_string(), Box::new(expr)));
        }
    }

    tokiter.reset_peek();
    parse_logical_or_expression(tokiter)
}

fn parse_statement(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Statement, ParseError> {
    let stmt = match tokiter.peek().unwrap().token {
        Token::Keyword(Keyword::Return) => {
            tokiter.next(); // consume
            Statement::Return(parse_expression(tokiter)?)
        }
        Token::Keyword(Keyword::Int) => {
            tokiter.next(); // consume

            let mut tok = tokiter.next().unwrap();
            let id = match &tok.token {
                Token::Identifier(n) => n,
                _ => {
                    return Err(ParseError {
                        cursor: tok.location,
                        message: format!("Invalid declaration statement. Expected an identifier, got '{}'.", tok.token),
                    })
                }
            };

            // parse initialization if next token is an assignment (equals sign)
            tok = tokiter.peek().unwrap();
            let init = match tok.token {
                Token::Assignment => {
                    tokiter.next(); // consume
                    Some(parse_expression(tokiter)?)
                }
                _ => {
                    tokiter.reset_peek();
                    None
                }
            };

            Statement::Decl(id.to_string(), init)
        }
        _ => {
            tokiter.reset_peek();
            // then we have an expression to parse
            Statement::Expr(parse_expression(tokiter)?)
        }
    };

    // ensure last token is a semicolon
    let tok = tokiter.next().unwrap();
    if let Token::Semicolon = tok.token {
    } else {
        return Err(ParseError {
            cursor: tok.location,
            message: format!("Invalid statement. Expected a final semicolon, got '{}'.", tok.token),
        });
    }

    Ok(stmt)
}

fn parse_function(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Function, ParseError> {
    // ensure first token is an Int keyword
    let mut tok = &tokiter.next().unwrap().token;

    if let Token::Keyword(Keyword::Int) = tok {
    } else {
        panic!("Invalid function declaration. Expected return type, got '{}'.", tok);
    }

    // next token should be an identifier
    tok = &tokiter.next().unwrap().token;
    let function_name = match tok {
        Token::Identifier(ident) => ident,
        _ => panic!("Invalid function declaration. Expected identifier, got '{}'.", tok),
    };

    // ensure next token is '('
    tok = &tokiter.next().unwrap().token;
    if let Token::Lparen = tok {
    } else {
        panic!("Invalid function declaration. Expected '(', got '{}'.", tok);
    }

    // ensure next token is ')'
    tok = &tokiter.next().unwrap().token;
    if let Token::Rparen = tok {
    } else {
        panic!("Invalid function declaration. Expected ')', got '{}'.", tok);
    }

    // ensure next token is '{'
    tok = &tokiter.next().unwrap().token;
    if let Token::Lbrace = tok {
    } else {
        panic!("Invalid function declaration. Expected '{{', got '{}'.", tok);
    }

    // parse statements
    let mut statements = Vec::new();

    loop {
        tok = &tokiter.peek().unwrap().token;
        if let Token::Rbrace = tok {
            break;
        }
        tokiter.reset_peek();
        statements.push(parse_statement(tokiter)?);
    }

    Ok(Function::Func(function_name.to_string(), statements))
}

fn parse_program(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Program, ParseError> {
    Ok(Program::Prog(parse_function(tokiter)?))
}

pub fn parse(tokens: &[TokNLoc]) -> Result<Program, ParseError> {
    let mut tokiter = itertools::multipeek(tokens.iter());
    parse_program(&mut tokiter)
}
