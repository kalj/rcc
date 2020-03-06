extern crate itertools;
use crate::tokenizer::{Keyword, TokNLoc, Token};
use core::slice::Iter;
use itertools::MultiPeek;
use std::error;
use std::fmt;

use crate::ast::{AssignmentKind, BinaryOp, FixOp, UnaryOp};
use crate::ast::{BlockItem, Expression, Function, Program, Statement};

//===================================================================
// Parsing
//===================================================================

#[derive(Debug, Clone)]
pub struct ParseError {
    pub cursor: usize,
    pub message: String,
}

impl ParseError {
    fn new(cursor: usize, message: String) -> ParseError {
        ParseError { cursor, message }
    }
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
                    message: "Invalid prefix expression. Expected variable identifier after prefix increment/decrement"
                        .to_string(),
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
                    message: "Invalid prefix expression. Expected variable identifier after prefix increment/decrement"
                        .to_string(),
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

fn parse_conditional_expression(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Expression, ParseError> {
    let loexpr = parse_logical_or_expression(tokiter)?;

    if let Token::QuestionMark = &tokiter.peek().unwrap().token {
        tokiter.next(); // consume

        let ifexpr = parse_expression(tokiter)?;

        let tok = tokiter.next().unwrap();
        if let Token::Colon = tok.token {
        } else {
            return Err(ParseError::new(
                tok.location,
                format!("Invalid conditional expression. Expected a colon, got '{}'.", tok.token),
            ));
        }

        let elseexpr = parse_conditional_expression(tokiter)?;

        Ok(Expression::Conditional(Box::new(loexpr), Box::new(ifexpr), Box::new(elseexpr)))
    } else {
        tokiter.reset_peek();
        Ok(loexpr)
    }
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
    parse_conditional_expression(tokiter)
}

fn ensure_semicolon(tokiter: &mut MultiPeek<Iter<TokNLoc>>, msg: &str) -> Result<(), ParseError> {
    // ensure last token is a semicolon
    let tok = tokiter.next().unwrap();
    if let Token::Semicolon = tok.token {
        Ok(())
    } else {
        Err(ParseError::new(tok.location, format!("{}. Expected a final semicolon, got '{}'.", msg, tok.token)))
    }
}

fn parse_statement(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Statement, ParseError> {
    let stmt = match tokiter.peek().unwrap().token {
        Token::Keyword(Keyword::Return) => {
            tokiter.next(); // consume
            let expr = parse_expression(tokiter)?;
            ensure_semicolon(tokiter, "Invalid return statement")?;
            Statement::Return(expr)
        }
        Token::Keyword(Keyword::If) => {
            tokiter.next(); // consume

            // ensure next token is '('
            let mut tok = tokiter.next().unwrap();
            if let Token::Lparen = tok.token {
            } else {
                return Err(ParseError::new(
                    tok.location,
                    format!("Invalid if statement. Expected '(', got '{}'.", tok.token),
                ));
            }

            let cond_expr = parse_expression(tokiter)?;

            // ensure next token is ')'
            tok = tokiter.next().unwrap();
            if let Token::Rparen = tok.token {
            } else {
                return Err(ParseError::new(
                    tok.location,
                    format!("Invalid if statement. Expected ')' after condition expression, got '{}'.", tok.token),
                ));
            }

            let if_stmnt = parse_statement(tokiter)?;

            if let Token::Keyword(Keyword::Else) = tokiter.peek().unwrap().token {
                tokiter.next(); // consume

                let else_stmnt = parse_statement(tokiter)?;

                Statement::If(cond_expr, Box::new(if_stmnt), Some(Box::new(else_stmnt)))
            } else {
                tokiter.reset_peek();
                Statement::If(cond_expr, Box::new(if_stmnt), None)
            }
        }
        _ => {
            tokiter.reset_peek();
            // then we have an expression to parse
            let expr = parse_expression(tokiter)?;
            ensure_semicolon(tokiter, "Invalid expression statement")?;
            Statement::Expr(expr)
        }
    };

    Ok(stmt)
}

fn parse_block_item(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<BlockItem, ParseError> {
    let bkitem = match tokiter.peek().unwrap().token {
        Token::Keyword(Keyword::Int) => {
            tokiter.next(); // consume

            let mut tok = tokiter.next().unwrap();
            let id = match &tok.token {
                Token::Identifier(n) => n,
                _ => {
                    return Err(ParseError::new(
                        tok.location,
                        format!("Invalid declaration. Expected an identifier, got '{}'.", tok.token),
                    ));
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

            // ensure last token is a semicolon
            ensure_semicolon(tokiter, "Invalid declaration")?;

            BlockItem::Decl(id.to_string(), init)
        }
        _ => {
            tokiter.reset_peek();
            // then we have an expression to parse
            BlockItem::Stmt(parse_statement(tokiter)?)
        }
    };

    Ok(bkitem)
}

fn parse_function(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Function, ParseError> {
    // ensure first token is an Int keyword
    let mut tok = tokiter.next().unwrap();

    if let Token::Keyword(Keyword::Int) = tok.token {
    } else {
        let msg = format!("Invalid function declaration. Expected return type, got '{}'.", tok.token);
        return Err(ParseError::new(tok.location, msg));
    }

    // next token should be an identifier
    tok = tokiter.next().unwrap();
    let function_name = match &tok.token {
        Token::Identifier(ident) => ident,
        _ => {
            let msg = format!("Invalid function declaration. Expected identifier, got '{}'.", tok.token);
            return Err(ParseError::new(tok.location, msg));
        }
    };

    // ensure next token is '('
    tok = tokiter.next().unwrap();
    if let Token::Lparen = tok.token {
    } else {
        let msg = format!("Invalid function declaration. Expected '(', got '{}'.", tok.token);
        return Err(ParseError::new(tok.location, msg));
    }

    // ensure next token is ')'
    tok = tokiter.next().unwrap();
    if let Token::Rparen = tok.token {
    } else {
        let msg = format!("Invalid function declaration. Expected ')', got '{}'.", tok.token);
        return Err(ParseError::new(tok.location, msg));
    }

    // ensure next token is '{'
    tok = tokiter.next().unwrap();
    if let Token::Lbrace = tok.token {
    } else {
        let msg = format!("Invalid function declaration. Expected '{{', got '{}'.", tok.token);
        return Err(ParseError::new(tok.location, msg));
    }

    // parse statements
    let mut block_items = Vec::new();

    loop {
        tok = tokiter.peek().unwrap();
        if let Token::Rbrace = tok.token {
            break;
        }
        tokiter.reset_peek();
        block_items.push(parse_block_item(tokiter)?);
    }

    Ok(Function::Func(function_name.to_string(), block_items))
}

fn parse_program(tokiter: &mut MultiPeek<Iter<TokNLoc>>) -> Result<Program, ParseError> {
    Ok(Program::Prog(parse_function(tokiter)?))
}

pub fn parse(tokens: &[TokNLoc]) -> Result<Program, ParseError> {
    let mut tokiter = itertools::multipeek(tokens.iter());
    parse_program(&mut tokiter)
}
