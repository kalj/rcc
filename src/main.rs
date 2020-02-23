extern crate clap;
extern crate regex;
extern crate itertools;
use clap::{App, Arg};
use core::slice::Iter;
use regex::Regex;
use std::error;
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};
use itertools::MultiPeek;
use std::collections::HashMap;

//===================================================================
// Tokenizing
//===================================================================

#[derive(Debug, Copy, Clone)]
enum Keyword {
    Int,
    Return,
}

#[derive(Debug, Clone)]
enum Token {
    Assignment,
    Semicolon,
    Lparen,
    Rparen,
    Lbrace,
    Rbrace,
    Multiplication,
    Division,
    Remainder,
    Plus,
    Minus,
    Not,
    Complement,
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
    AdditionAssignment,
    SubtractionAssignment,
    MultiplicationAssignment,
    DivisionAssignment,
    RemainderAssignment,
    BitwiseXorAssignment,
    BitwiseOrAssignment,
    BitwiseAndAssignment,
    LeftShiftAssignment,
    RightShiftAssignment,
    Increment,
    Decrement,
    Keyword(Keyword),
    Identifier(String),
    IntLiteral(i64),
}

fn keyword_to_str(kw: &Keyword) -> String {
    match kw {
        Keyword::Int => "int".to_string(),
        Keyword::Return => "return".to_string(),
    }
}

fn token_to_str(tok: &Token) -> String {
    match tok {
        Token::Assignment => "=".to_string(),
        Token::Lparen => "(".to_string(),
        Token::Rparen => ")".to_string(),
        Token::Lbrace => "{".to_string(),
        Token::Rbrace => "}".to_string(),
        Token::Semicolon => ";".to_string(),
        Token::Multiplication => "*".to_string(),
        Token::Division => "/".to_string(),
        Token::Remainder => "%".to_string(),
        Token::Plus => "+".to_string(),
        Token::Minus => "-".to_string(),
        Token::Not => "!".to_string(),
        Token::Complement => "~".to_string(),
        Token::LogicalAnd => "&&".to_string(),
        Token::LogicalOr => "||".to_string(),
        Token::Equal => "==".to_string(),
        Token::NotEqual => "!=".to_string(),
        Token::Less => "<".to_string(),
        Token::Greater => ">".to_string(),
        Token::LessEqual => "<=".to_string(),
        Token::GreaterEqual => ">=".to_string(),
        Token::BitwiseAnd => "&".to_string(),
        Token::BitwiseOr => "|".to_string(),
        Token::BitwiseXor => "^".to_string(),
        Token::LeftShift => "<<".to_string(),
        Token::RightShift => ">>".to_string(),
        Token::AdditionAssignment => "+=".to_string(),
        Token::SubtractionAssignment => "-=".to_string(),
        Token::MultiplicationAssignment => "*=".to_string(),
        Token::DivisionAssignment => "/=".to_string(),
        Token::RemainderAssignment => "%=".to_string(),
        Token::BitwiseXorAssignment => "^=".to_string(),
        Token::BitwiseOrAssignment => "|=".to_string(),
        Token::BitwiseAndAssignment => "&=".to_string(),
        Token::LeftShiftAssignment => "<<=".to_string(),
        Token::RightShiftAssignment => ">>=".to_string(),
        Token::Increment => "++".to_string(),
        Token::Decrement => "--".to_string(),
        Token::Keyword(kw) => keyword_to_str(kw),
        Token::Identifier(ident) => ident.to_string(),
        Token::IntLiteral(val) => val.to_string(),
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", token_to_str(self))
    }
}

fn token_length(tok: &Token) -> usize {
    token_to_str(tok).len()
}

fn get_token_pattern(tok: &Token) -> String {
    match tok {
        Token::Keyword(kw) => format!(r"^{}\W",keyword_to_str(kw)),
        Token::Identifier(_) => r"^([a-zA-Z]\w*)".to_string(),
        Token::IntLiteral(_) => r"^([0-9]+)".to_string(),
        _ => format!("^{}",regex::escape(&token_to_str(tok)))
    }
}

#[derive(Debug, Clone)]
struct TokenError {
    cursor: usize,
}

impl fmt::Display for TokenError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Unexpected token at {}", self.cursor)
    }
}

impl error::Error for TokenError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }
}

fn get_token(source: &str, cursor: usize) -> Result<Token, TokenError> {
    let toktypes = [
        // patterns of length 3
        Token::LeftShiftAssignment,
        Token::RightShiftAssignment,
        // patterns of length 2
        Token::LogicalAnd,
        Token::LogicalOr,
        Token::Equal,
        Token::NotEqual,
        Token::LessEqual,
        Token::GreaterEqual,
        Token::LeftShift,
        Token::RightShift,
        Token::AdditionAssignment,
        Token::SubtractionAssignment,
        Token::MultiplicationAssignment,
        Token::DivisionAssignment,
        Token::RemainderAssignment,
        Token::BitwiseXorAssignment,
        Token::BitwiseOrAssignment,
        Token::BitwiseAndAssignment,
        Token::Increment,
        Token::Decrement,
        // patterns of length 1
        Token::Semicolon,
        Token::Lparen,
        Token::Rparen,
        Token::Lbrace,
        Token::Rbrace,
        Token::Lbrace,
        Token::Rbrace,
        Token::Multiplication,
        Token::Division,
        Token::Remainder,
        Token::Plus,
        Token::Minus,
        Token::BitwiseAnd,
        Token::BitwiseOr,
        Token::BitwiseXor,
        Token::Less,
        Token::Greater,
        Token::Not,
        Token::Complement,
        Token::Assignment,
        // generic patterns
        Token::Keyword(Keyword::Int),
        Token::Keyword(Keyword::Return),
        Token::Identifier("a".to_string()), // with placeholder
        Token::IntLiteral(1),               // with placeholder
    ];

    for t in toktypes.iter() {
        let re = Regex::new(&get_token_pattern(t)).expect(&format!(
            "Failed building regex object for token type {:?}",
            t
        ));
        if let Some(captures) = re.captures(&source[cursor..]) {
            return match t {
                Token::Identifier(_) => {
                    let ident_cap = captures.get(1).expect("asdfb");
                    let ident = ident_cap.as_str().to_string();
                    Ok(Token::Identifier(ident))
                }

                Token::IntLiteral(_) => {
                    let value: i64 = captures.get(1).unwrap().as_str().parse().unwrap();
                    Ok(Token::IntLiteral(value))
                }
                Token::Keyword(kw) => {
                    Ok(Token::Keyword(*kw))
                }
                _ => {
                    Ok(t.clone())
                }
            };
        }
    }
    return Err(TokenError { cursor: cursor });
}

struct TokNLoc {
    token: Token,
    location: usize,
    length: usize
}

impl TokNLoc {
    fn new(tok: Token, loc: usize, len: usize) -> TokNLoc {
        TokNLoc { token: tok, location: loc, length: len }
    }
}

fn tokenize(source: &str) -> Vec<TokNLoc> {
    let mut result = Vec::new();

    let len = source.len();
    let mut cursor = 0;

    let re_space = Regex::new(r"^\p{White_Space}").unwrap();

    while cursor < len {
        if re_space.is_match(&source[cursor..]) {
            cursor += 1;
            continue;
        }

        let tok = get_token(source, cursor).unwrap();
        let toklen = token_length(&tok);
        result.push(TokNLoc::new(tok,cursor,toklen));
        cursor += toklen;
    }

    return result;
}

#[derive(Debug)]
enum BinaryOp {
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
enum UnaryOp {
    Negate,
    Not,
    Complement,
}

#[derive(Debug)]
enum AssignmentKind {
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
enum FixOp {
    Inc,
    Dec
}

#[derive(Debug)]
enum Expression {
    Assign(AssignmentKind, String, Box<Expression>),
    BinaryOp(BinaryOp, Box<Expression>, Box<Expression>),
    UnaryOp(UnaryOp, Box<Expression>),
    PrefixOp(FixOp, String),
    PostfixOp(FixOp, String),
    Constant(i64),
    Variable(String)
}

#[derive(Debug)]
enum Statement {
    Return(Expression),
    Decl(String, Option<Expression>),
    Expr(Expression),
}

#[derive(Debug)]
enum Function {
    Func(String, Vec<Statement>),
}

#[derive(Debug)]
enum Program {
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
        Statement::Decl(id,init) => {
            if let Some(expr) = init {
                println!("{: <1$}Decl {2:?} {{", "", (lvl * 2) as usize, id);
                print_expression(expr, lvl + 1);
                println!("{: <1$}}}", "", (lvl * 2) as usize);
            }
            else {
                println!("{: <1$}Decl {2:?}", "", (lvl * 2) as usize, id);
            }
        }
        Statement::Expr(expr) => {
            println!("{: <1$}Expr {{", "", (lvl * 2) as usize);
            print_expression(expr, lvl+1);
            println!("{: <1$}}}", "", (lvl * 2) as usize);
        }
    }
}


fn print_program(prog: &Program) {
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
struct ParseError {
    cursor: usize,
    message: String
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

fn parse_postfix_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression,ParseError> {
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

fn parse_prefix_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression,ParseError> {
    let tok = tokiter.peek().unwrap();
    match &tok.token {
        Token::Minus => {
            tokiter.next(); // consume
            let operand = parse_postfix_expression(tokiter)?;
            Ok(Expression::UnaryOp(UnaryOp::Negate, Box::new(operand)))
        },
        Token::Not => {
            tokiter.next(); // consume
            let operand = parse_postfix_expression(tokiter)?;
            Ok(Expression::UnaryOp(UnaryOp::Not, Box::new(operand)))
        },
        Token::Complement => {
            tokiter.next(); // consume
            let operand = parse_postfix_expression(tokiter)?;
            Ok(Expression::UnaryOp(UnaryOp::Complement, Box::new(operand)))
        },
        Token::Increment => {
            tokiter.next(); // consume

            let next_loc = tokiter.peek().unwrap().location; // for error message
            tokiter.reset_peek();

            let operand = parse_postfix_expression(tokiter)?;
            if let Expression::Variable(id) = operand {
                Ok(Expression::PrefixOp(FixOp::Inc,id))
            }
            else {
                Err(ParseError{cursor:next_loc, message:format!("Invalid prefix expression. Expected variable identifier after prefix increment/decrement")})
            }
        }
        Token::Decrement => {
            tokiter.next(); // consume

            let next_loc = tokiter.peek().unwrap().location; // for error message
            tokiter.reset_peek();

            let operand = parse_postfix_expression(tokiter)?;
            if let Expression::Variable(id) = operand {
                Ok(Expression::PrefixOp(FixOp::Dec,id))
            }
            else {
                Err(ParseError{cursor:next_loc, message:format!("Invalid prefix expression. Expected variable identifier after prefix increment/decrement")})
            }
        }
        _ => {
            tokiter.reset_peek();
            parse_postfix_expression(tokiter)
        }
    }
}

fn parse_multiplicative_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression,ParseError> {
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
    return Ok(factor);
}

fn parse_additive_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression,ParseError> {

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
    return Ok(term);
}

fn parse_shift_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression,ParseError> {
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
    return Ok(adexpr);
}

fn parse_relational_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression,ParseError> {
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
    return Ok(shiftexpr);
}

fn parse_equality_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression,ParseError> {
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
    return Ok(relexpr);
}

fn parse_bitwise_and_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression,ParseError> {
    let mut eqexpr = parse_equality_expression(tokiter)?;

    while let Some(tok) = tokiter.peek() {
        if let Token::BitwiseAnd = tok.token {
            tokiter.next(); // consume
            let next_eqexpr = parse_equality_expression(tokiter)?;
            eqexpr = Expression::BinaryOp(
                BinaryOp::BitwiseAnd,
                Box::new(eqexpr),
                Box::new(next_eqexpr),
            );
        }
        else {
            break;
        }
    }
    tokiter.reset_peek();
    return Ok(eqexpr);
}

fn parse_bitwise_xor_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression,ParseError> {
    let mut bandexpr = parse_bitwise_and_expression(tokiter)?;

    while let Some(tok) = tokiter.peek() {
        if let Token::BitwiseXor = tok.token {
            tokiter.next(); // consume
            let next_bandexpr = parse_bitwise_and_expression(tokiter)?;
            bandexpr = Expression::BinaryOp(
                BinaryOp::BitwiseXor,
                Box::new(bandexpr),
                Box::new(next_bandexpr),
            );
        }
        else {
            break;
        }
    }
    tokiter.reset_peek();
    return Ok(bandexpr);
}

fn parse_bitwise_or_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression,ParseError> {
    let mut bxorexpr = parse_bitwise_xor_expression(tokiter)?;

    while let Some(tok) = tokiter.peek() {
        if let Token::BitwiseOr = tok.token {
            tokiter.next(); // consume
            let next_bxorexpr = parse_bitwise_xor_expression(tokiter)?;
            bxorexpr = Expression::BinaryOp(
                BinaryOp::BitwiseOr,
                Box::new(bxorexpr),
                Box::new(next_bxorexpr),
            );
        }
        else {
            break;
        }
    }
    tokiter.reset_peek();
    return Ok(bxorexpr);
}

fn parse_logical_and_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression,ParseError> {
    let mut borexpr = parse_bitwise_or_expression(tokiter)?;

    while let Some(tok) = tokiter.peek() {
        if let Token::LogicalAnd = tok.token {
            tokiter.next(); // consume
            let next_borexpr = parse_bitwise_or_expression(tokiter)?;
            borexpr = Expression::BinaryOp(
                BinaryOp::LogicalAnd,
                Box::new(borexpr),
                Box::new(next_borexpr),
            );
        }
        else {
            break;
        }
    }
    tokiter.reset_peek();
    return Ok(borexpr);
}

fn parse_logical_or_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression,ParseError> {

    let mut laexpr = parse_logical_and_expression(tokiter)?;

    while let Some(tok) = tokiter.peek() {
        if let Token::LogicalOr = tok.token {
            tokiter.next(); // consume
            let next_laexpr = parse_logical_and_expression(tokiter)?;
            laexpr = Expression::BinaryOp(
                BinaryOp::LogicalOr,
                Box::new(laexpr),
                Box::new(next_laexpr),
            );
        }
        else {
            break;
        }
    }
    tokiter.reset_peek();
    return Ok(laexpr);
}

fn parse_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression,ParseError> {

    match &tokiter.peek().unwrap().token {
        Token::Identifier(id) => {

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
                return Ok(Expression::Assign(asskind, id.to_string(), Box::new(expr)))
            }
        }
        _ => ()
    }

    tokiter.reset_peek();
    return parse_logical_or_expression(tokiter);
}

fn parse_statement(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Statement,ParseError> {

    let stmt = match tokiter.peek().unwrap().token {
        Token::Keyword(Keyword::Return) => {
            tokiter.next(); // consume
            Statement::Return(parse_expression(tokiter)?)
        },
        Token::Keyword(Keyword::Int) => {
            tokiter.next(); // consume

            let mut tok = tokiter.next().unwrap();
            let id =
                match &tok.token {
                    Token::Identifier(n) => n,
                    _ => return Err(ParseError{cursor:tok.location, message:format!("Invalid declaration statement. Expected an identifier, got '{}'.", tok.token)})
                };

            // parse initialization if next token is an assignment (equals sign)
            tok = tokiter.peek().unwrap();
            let init = match tok.token {
                Token::Assignment => {
                    tokiter.next(); // consume
                    Some(parse_expression(tokiter)?)
                },
                _ => {
                    tokiter.reset_peek();
                    None
                }
            };

            Statement::Decl(id.to_string(), init)
        },
        _ => {
            tokiter.reset_peek();
            // then we have an expression to parse
            Statement::Expr(parse_expression(tokiter)?)
        }
    };

    // ensure last token is a semicolon
    let tok = tokiter.next().unwrap();
    if let Token::Semicolon = tok.token {}
    else {
        return Err(ParseError{cursor:tok.location, message:format!("Invalid statement. Expected a final semicolon, got '{}'.", tok.token)});
    }

    return Ok(stmt);
}

fn parse_function(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Function,ParseError> {
    // ensure first token is an Int keyword
    let mut tok = &tokiter.next().unwrap().token;

    if let Token::Keyword(Keyword::Int) = tok {}
    else {
        panic!("Invalid function declaration. Expected return type, got '{}'.", tok);
    }

    // next token should be an identifier
    tok = &tokiter.next().unwrap().token;
    let function_name = match tok {
        Token::Identifier(ident) => ident,
        _ => panic!(
            "Invalid function declaration. Expected identifier, got '{}'.",
            tok
        ),
    };

    // ensure next token is '('
    tok = &tokiter.next().unwrap().token;
    if let Token::Lparen = tok {}
    else {
        panic!("Invalid function declaration. Expected '(', got '{}'.", tok);
    }

    // ensure next token is ')'
    tok = &tokiter.next().unwrap().token;
    if let Token::Rparen = tok {}
    else {
        panic!("Invalid function declaration. Expected ')', got '{}'.", tok);
    }

    // ensure next token is '{'
    tok = &tokiter.next().unwrap().token;
    if let Token::Lbrace = tok {}
    else {
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

    return Ok(Function::Func(function_name.to_string(), statements));
}

fn parse_program(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Program,ParseError> {
    return Ok(Program::Prog(parse_function(tokiter)?));
}

fn parse(tokens: &[TokNLoc]) -> Result<Program,ParseError> {
    let mut tokiter = itertools::multipeek(tokens.iter());
    return parse_program(&mut tokiter);
}

//===================================================================
// Code generation
//===================================================================

enum CodeLine {
    LabelRef(String),
    Instr1(String),
    Instr2(String, String),
    Instr3(String, String, String),
}

impl CodeLine {
    fn lbl(l: &str) -> CodeLine {
        CodeLine::LabelRef(l.to_string())
    }

    fn i1(opcode: &str) -> CodeLine {
        CodeLine::Instr1(opcode.to_string())
    }

    fn i2(opcode: &str, op1: &str) -> CodeLine {
        CodeLine::Instr2(opcode.to_string(), op1.to_string())
    }

    fn i3(opcode: &str, op1: &str, op2: &str) -> CodeLine {
        CodeLine::Instr3(opcode.to_string(), op1.to_string(), op2.to_string())
    }
}

struct Code {
    code: Vec<CodeLine>,
}

impl Code {
    fn new() -> Code {
        Code { code: Vec::new() }
    }

    fn push(&mut self, cl: CodeLine) {
        self.code.push(cl)
    }

    fn append(&mut self, mut more: Code) {
        self.code.append(&mut more.code);
    }

    fn get_str(self) -> String {
        let strs: Vec<String> = self
            .code
            .iter()
            .map(|cl| match cl {
                CodeLine::LabelRef(lbl) => format!("{}:", lbl),
                CodeLine::Instr1(opcode) => format!("    {}", opcode),
                CodeLine::Instr2(opcode, operand) => format!("    {} {}", opcode, operand),
                CodeLine::Instr3(opcode, operand1, operand2) => {
                    format!("    {} {}, {}", opcode, operand1, operand2)
                }
            })
            .collect();
        return strs.join("\n") + "\n";
    }
}

struct Generator {
    emit_32bit: bool,
    label_counter: i32,
    rega: String,
    regc: String,
    regbp: String,
    regsp: String,
    rega32: String,
    regc32: String,
    regd32: String,
    bytes_per_reg: usize,
    var_map: HashMap<String,i32>,
    var_stack_index: i32,
}

impl Generator {
    fn new(emit_32bit: bool) -> Generator {
        let bytes_per_reg = if emit_32bit { 4 } else { 8 };
        Generator {
            emit_32bit: emit_32bit,
            label_counter: 0,
            rega: (if emit_32bit { "%eax" } else { "%rax" }).to_string(),
            regc: (if emit_32bit { "%ecx" } else { "%rcx" }).to_string(),
            regbp: (if emit_32bit { "%ebp" } else { "%rbp" }).to_string(),
            regsp: (if emit_32bit { "%esp" } else { "%rsp" }).to_string(),
            rega32: "%eax".to_string(),
            regc32: "%ecx".to_string(),
            regd32: "%edx".to_string(),
            bytes_per_reg: bytes_per_reg,
            var_map: HashMap::new(),
            var_stack_index: -(bytes_per_reg as i32),
        }
    }

    fn generate_binop_code(&self, binop: &BinaryOp) -> Code {
        let mut code = Code::new();

        match binop {
            BinaryOp::Addition => {
                code.push(CodeLine::i3("add", &self.regc32, &self.rega32)); //   add, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
            }
            BinaryOp::Subtraction => {
                code.push(CodeLine::i3("sub", &self.regc32, &self.rega32)); //   subtract %eax (arg1) - %ecx (arg2) -> %eax
            }
            BinaryOp::Multiplication => {
                code.push(CodeLine::i3("imul", &self.regc32, &self.rega32)); //  multiply, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
            }
            BinaryOp::Division|BinaryOp::Remainder => {
                code.push(CodeLine::i1("cltd")); //                sign extend %eax into %edx:%eax
                code.push(CodeLine::i2("idiv", &self.regc32)); //  idiv takes numerator in %eax, denominator in arg (%ecx). quotient is put in %eax, remainder in %edx.
                if let BinaryOp::Remainder = binop {
                    code.push(CodeLine::i3("mov", &self.regd32, &self.rega32)); //   copy remainder into %eax
                }
            }
            BinaryOp::Equal => {
                code.push(CodeLine::i3("cmp", &self.regc32, &self.rega32)); //    set ZF if EAX == ECX
                code.push(CodeLine::i3("mov", "$0", &self.rega32)); //            zero out EAX without changing ZF
                code.push(CodeLine::i2("sete", "%al")); //                        set bit to 1 if ecx (op1) was equal to eax (op2)
            }
            BinaryOp::NotEqual => {
                code.push(CodeLine::i3("cmp", &self.regc32, &self.rega32)); //    set ZF if EAX == ECX
                code.push(CodeLine::i3("mov", "$0", &self.rega32)); //            zero out EAX without changing ZF
                code.push(CodeLine::i2("setne", "%al")); //                       set bit to 1 if ecx (op1) was not equal to eax (op2)
            }
            BinaryOp::Less => {
                code.push(CodeLine::i3("cmp", &self.regc32, &self.rega32)); //    compare ECX and EAX
                code.push(CodeLine::i3("mov", "$0", &self.rega32)); //            zero out EAX without changing ZF
                code.push(CodeLine::i2("setl", "%al")); //                        set bit to 1 if ecx (op1) was less than eax (op2)
            }
            BinaryOp::Greater => {
                code.push(CodeLine::i3("cmp", &self.regc32, &self.rega32)); //    compare ECX and EAX
                code.push(CodeLine::i3("mov", "$0", &self.rega32)); //            zero out EAX without changing ZF
                code.push(CodeLine::i2("setg", "%al")); //                        set bit to 1 if ecx (op1) was greater than eax (op2)
            }
            BinaryOp::LessEqual => {
                code.push(CodeLine::i3("cmp", &self.regc32, &self.rega32)); //    compare ECX and EAX
                code.push(CodeLine::i3("mov", "$0", &self.rega32)); //            zero out EAX without changing ZF
                code.push(CodeLine::i2("setle", "%al")); //                       set bit to 1 if ecx (op1) was less than or equal to eax (op2)
            }
            BinaryOp::GreaterEqual => {
                code.push(CodeLine::i3("cmp", &self.regc32, &self.rega32)); //    compare ECX and EAX
                code.push(CodeLine::i3("mov", "$0", &self.rega32)); //            zero out EAX without changing ZF
                code.push(CodeLine::i2("setge", "%al")); //                       set bit to 1 if ecx (op1) was greater than or equal to eax (op2)
            }
            BinaryOp::BitwiseOr => {
                code.push(CodeLine::i3("or", &self.regc32, &self.rega32)); //    and, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
            }
            BinaryOp::BitwiseXor => {
                code.push(CodeLine::i3("xor", &self.regc32, &self.rega32)); //   and, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
            }
            BinaryOp::BitwiseAnd => {
                code.push(CodeLine::i3("and", &self.regc32, &self.rega32)); //   and, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
            }
            BinaryOp::LeftShift => {
                code.push(CodeLine::i3("sal", "%cl", &self.rega32)); //          do arithmetic left shift (== logical left shift), %eax = %eax << %cl
            }
            BinaryOp::RightShift => {
                code.push(CodeLine::i3("sar", "%cl", &self.rega32)); //          do arithmetic right shift, %eax = %eax >> %cl
            }
            BinaryOp::LogicalAnd | BinaryOp::LogicalOr => {
                panic!("Internal Error"); // Handled above separately
            }
        }

        return code;
    }

    fn generate_expression_code(&mut self, expr: &Expression) -> Code {
        let mut code = Code::new();
        match expr {
            Expression::Assign(kind, id, expr) => {
                code = self.generate_expression_code(expr);
                let var_offset = self.var_map[id];

                let binop = match kind {
                    AssignmentKind::Write => None,
                    AssignmentKind::Add => Some(BinaryOp::Addition),
                    AssignmentKind::Subtract => Some(BinaryOp::Subtraction),
                    AssignmentKind::Multiply => Some(BinaryOp::Multiplication),
                    AssignmentKind::Divide => Some(BinaryOp::Division),
                    AssignmentKind::Remainder => Some(BinaryOp::Remainder),
                    AssignmentKind::BitwiseOr => Some(BinaryOp::BitwiseOr),
                    AssignmentKind::BitwiseXor => Some(BinaryOp::BitwiseXor),
                    AssignmentKind::BitwiseAnd => Some(BinaryOp::BitwiseAnd),
                    AssignmentKind::LeftShift => Some(BinaryOp::LeftShift),
                    AssignmentKind::RightShift => Some(BinaryOp::RightShift)
                };

                if let Some(bop) = binop {
                    code.push(CodeLine::i3("mov", &self.rega32, &self.regc32));
                    code.push(CodeLine::i3("mov", &format!("{}({})", var_offset, self.regbp), &self.rega32));
                    code.append(self.generate_binop_code(&bop));
                }

                code.push(CodeLine::i3("mov", &self.rega32, &format!("{}({})", var_offset, self.regbp)));
            }
            Expression::Variable(id) => {
                let var_offset = self.var_map[id];
                code.push(CodeLine::i3("mov",&format!("{}({})", var_offset, self.regbp), &self.rega));
            }
            Expression::BinaryOp(BinaryOp::LogicalOr, e1, e2) => {
                // setup labels
                let cond2 = format!("_label{}", self.label_counter);
                let end = format!("_label{}", self.label_counter + 1);
                self.label_counter += 2;

                code = self.generate_expression_code(e1);
                // if true then just jump over second part and set true
                // else evaluate second part and set to return status of that
                code.push(CodeLine::i3("cmp", "$0", &self.rega32)); //               set ZF if EAX == 0
                code.push(CodeLine::i2("je", &cond2)); //                            if ZF is set, go to cond2
                code.push(CodeLine::i3("mov", "$1", &self.rega32)); //               else we are done, so set result to 1,
                code.push(CodeLine::i2("jmp", &end)); //                             and jump to end.
                code.push(CodeLine::lbl(&cond2));
                code.append(self.generate_expression_code(e2));
                code.push(CodeLine::i3("cmp", "$0", &self.rega32)); //               set ZF if EAX == 0
                code.push(CodeLine::i3("mov", "$0", &self.rega32)); //               zero out EAX without changing ZF
                code.push(CodeLine::i2("setnz", "%al")); //                          set bit to 1 if eax was not zero
                code.push(CodeLine::lbl(&end));
            }
            Expression::BinaryOp(BinaryOp::LogicalAnd, e1, e2) => {
                // setup labels
                let cond2 = format!("_label{}", self.label_counter);
                let end = format!("_label{}", self.label_counter + 1);
                self.label_counter += 2;

                code = self.generate_expression_code(e1);
                // if false then just jump over second part and set false
                // else evaluate second part and set to return status of that
                code.push(CodeLine::i3("cmp", "$0", &self.rega32)); //               set ZF if EAX == 0
                code.push(CodeLine::i2("jne", &cond2)); //                           if ZF is not, go to cond2
                code.push(CodeLine::i2("jmp", &end)); //                             else we are done (and eax is 0), so jump to end.
                code.push(CodeLine::lbl(&cond2));
                code.append(self.generate_expression_code(e2));
                code.push(CodeLine::i3("cmp", "$0", &self.rega32)); //               set ZF if EAX == 0
                code.push(CodeLine::i3("mov", "$0", &self.rega32)); //               zero out EAX without changing ZF
                code.push(CodeLine::i2("setnz", "%al")); //                          set bit to 1 if eax was not zero
                code.push(CodeLine::lbl(&end));
            }
            Expression::BinaryOp(bop, e1, e2) => {
                code = self.generate_expression_code(e1);

                code.push(CodeLine::i2("push", &self.rega));
                code.append(self.generate_expression_code(e2));

                code.push(CodeLine::i3("mov", &self.rega32, &self.regc32)); //   copy arg2 into %ecx
                code.push(CodeLine::i2("pop", &self.rega)); //                   get arg1 from stack into %eax
                code.append(self.generate_binop_code(bop))
            }
            Expression::UnaryOp(uop, expr) => {
                code = self.generate_expression_code(expr);
                match uop {
                    UnaryOp::Negate => {
                        code.push(CodeLine::i2("neg", &self.rega32));
                    }
                    UnaryOp::Not => {
                        code.push(CodeLine::i3("cmp", "$0", &self.rega32));
                        code.push(CodeLine::i3("mov", "$0", &self.rega32));
                        code.push(CodeLine::i2("sete", "%al"));
                    }
                    UnaryOp::Complement => {
                        code.push(CodeLine::i2("not", &self.rega32));
                    }
                }
            }
            Expression::PrefixOp(fixop, id) => {

                let var_offset = self.var_map[id];
                if let FixOp::Inc = fixop {
                    code.push(CodeLine::i2("incl", &format!("{}({})", var_offset, self.regbp)));
                }
                else {
                    code.push(CodeLine::i2("decl", &format!("{}({})", var_offset, self.regbp)));
                }
                code.push(CodeLine::i3("mov",&format!("{}({})", var_offset, self.regbp), &self.rega));
            }
            Expression::PostfixOp(fixop, id) => {

                let var_offset = self.var_map[id];
                code.push(CodeLine::i3("mov",&format!("{}({})", var_offset, self.regbp), &self.rega));
                if let FixOp::Inc = fixop {
                    code.push(CodeLine::i2("incl", &format!("{}({})", var_offset, self.regbp)));
                }
                else {
                    code.push(CodeLine::i2("decl", &format!("{}({})", var_offset, self.regbp)));
                }
            }
            Expression::Constant(val) => {
                let literal = format!("${}", val);
                code.push(CodeLine::i3("mov", &literal, &self.rega32));
            }
        }
        return code;
    }

    fn generate_statement_code(&mut self, stmnt: Statement) -> Code {
        let mut code = Code::new();
        match stmnt {
            Statement::Return(expr) => {
                code = self.generate_expression_code(&expr);
                code.push(CodeLine::i3("mov", &self.regbp, &self.regsp));
                code.push(CodeLine::i2("pop", &self.regbp));
                code.push(CodeLine::i1("ret"));
            }
            Statement::Decl(id, init) => {
                if self.var_map.contains_key(&id) {
                    panic!("Variable {} already declared",id);
                }
                if let Some(expr) = init {
                    code = self.generate_expression_code(&expr);      // possibly compute initial value, saved in %rax
                }
                else {
                    code.push(CodeLine::i3("mov", "$0", &self.rega)); // otherwise initialize %rax with 0
                }
                code.push(CodeLine::i2("push", &self.rega));          // push value on stack at known index
                self.var_map.insert(id, self.var_stack_index);        // save name and stack offset
                self.var_stack_index -= self.bytes_per_reg as i32;    // update stack index

            }
            Statement::Expr(expr) => {
               code = self.generate_expression_code(&expr);
            }
        }
        return code;
    }

    fn generate_function_code(&mut self, func: Function) -> Code {
        let mut code = Code::new();

        let Function::Func(name, body) = func;
        code.push(CodeLine::i2(".globl", &name));
        code.push(CodeLine::lbl(&name));
        code.push(CodeLine::i2("push", &self.regbp));
        code.push(CodeLine::i3("mov", &self.regsp, &self.regbp));
        for stmt in body {
            code.append(self.generate_statement_code(stmt));
        }

        if ! code.code.iter().any(|cl| {
            if let CodeLine::Instr1(op) = cl {
                op=="ret"
            }
            else {
                false
            }
        }) {
            code.append(self.generate_statement_code(Statement::Return(Expression::Constant(0))));
        }
        return code;
    }

    fn generate_program_code(&mut self, prog: Program) -> Code {
        let Program::Prog(func) = prog;
        let code = self.generate_function_code(func);
        return code;
    }
}

fn main() {
    let matches = App::new("c-compiler")
        .arg(
            Arg::with_name("INPUT")
                .help("The source file to compile")
                .required(true),
        )
        .arg(
            Arg::with_name("output")
                .short("o")
                .long("output")
                .value_name("OUTPUT")
                .help("The output assembly file (INPUT with suffix .s by default)"),
        )
        .arg(
            Arg::with_name("BITS")
                .short("m")
                .possible_values(&["64", "32"])
                .default_value("64")
                .help("Specify 32 or 64 bit code generation."),
        )
        .arg(
            Arg::with_name("verbose")
                .short("v")
                .long("verbose")
                .help("Enable verbose output"),
        )
        .get_matches();

    let source_filename = matches.value_of("INPUT").unwrap();
    let source_path = Path::new(source_filename);

    let emit_32bit = matches.value_of("BITS").unwrap() == "32";
    let verbose = matches.is_present("verbose");

    match source_path.extension() {
        Some(x) if x.to_str() == Some("c") => (),
        _ => {
            println!("Expected c source file with extension .c");
            std::process::exit(1)
        }
    }

    let output_path: PathBuf = match matches.value_of("OUTPUT") {
        Some(p) => PathBuf::from(p),
        None => source_path.with_extension("s"),
    };

    if verbose {
        println!(
            "Compiling {} -> {}...",
            source_path.display(),
            output_path.display()
        );
    }

    let source = fs::read_to_string(source_path).expect("Failed reading source file");

    if verbose {
        println!("Got source:");
        println!("{}", source);
    }

    let tokens = tokenize(&source);

    if verbose {
        println!("After tokenization:");
        let tokenstrs: Vec<String> = tokens.iter().map(|t| format!("{}", t.token)).collect();
        println!("{}", tokenstrs.join(" "));
    }

    let program = match parse(&tokens) {
        Ok(prog) => prog,
        Err(err) => {
            let mut line_starts = Vec::new();
            line_starts.push(0 as usize);
            let re = Regex::new(r"\n").unwrap();
            for m in re.find_iter(&source) {
                line_starts.push(m.start()+1);
            }

            line_starts.push(source.len()); // put the end of file last

            let row = line_starts.iter().rposition(|ls| { ls <= &err.cursor }).unwrap();
            let col = err.cursor - line_starts[row];
            let rowstart = line_starts[row];
            let rowend = line_starts[row+1];

            println!("{}:{}:{}:ParseError: {}",source_path.display(), row, col, err.message);
            println!("{}",&source[rowstart..rowend]);
            println!("{:<1$}^", "", col);
            std::process::exit(1);
        }
    };

    if verbose {
        println!("After parsing:");
        print_program(&program);
    }

    let mut generator = Generator::new(emit_32bit);
    let assembly_code = generator.generate_program_code(program);

    fs::write(output_path, assembly_code.get_str()).expect("Failed writing assembly output");
}
