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

fn mkperr(tok: &TokNLoc, msg: &str) -> ParseError {
    ParseError { cursor: tok.location, message: format!("{}, got '{}'.", msg, tok.token) }
}

pub struct Parser<'a> {
    tokiter: MultiPeek<Iter<'a, TokNLoc>>,
}

impl Parser<'_> {
    pub fn new(tokens: &[TokNLoc]) -> Parser {
        Parser { tokiter: itertools::multipeek(tokens.iter()) }
    }

    pub fn parse(&mut self) -> Result<Program, ParseError> {
        self.parse_program()
    }

    fn parse_postfix_expression(&mut self) -> Result<Expression, ParseError> {
        let tok = self.tokiter.next().unwrap();
        match &tok.token {
            Token::Lparen => {
                let subexpr = self.parse_expression()?;
                let tok = &self.tokiter.next().unwrap();
                match tok.token {
                    Token::Rparen => Ok(subexpr),
                    _ => Err(mkperr(tok, "Missing closing parenthesis after expression")),
                }
            }
            Token::Identifier(id) => {
                match self.tokiter.peek().unwrap().token {
                    Token::Increment => {
                        self.tokiter.next(); // consume
                        Ok(Expression::PostfixOp(FixOp::Inc, id.to_string()))
                    }
                    Token::Decrement => {
                        self.tokiter.next(); // consume
                        Ok(Expression::PostfixOp(FixOp::Dec, id.to_string()))
                    }
                    _ => {
                        self.tokiter.reset_peek();
                        Ok(Expression::Variable(id.to_string()))
                    }
                }
            }
            Token::IntLiteral(v) => Ok(Expression::Constant(*v)),
            _ => Err(mkperr(
                tok,
                "Invalid postfix expression. \
                                 Expected int literal, (expr), or identifier \
                                 possibly with postfix operator",
            )),
        }
    }

    fn parse_prefix_expression(&mut self) -> Result<Expression, ParseError> {
        let tok = self.tokiter.peek().unwrap();
        match &tok.token {
            Token::Minus => {
                self.tokiter.next(); // consume
                let operand = self.parse_prefix_expression()?;
                Ok(Expression::UnaryOp(UnaryOp::Negate, Box::new(operand)))
            }
            Token::Not => {
                self.tokiter.next(); // consume
                let operand = self.parse_prefix_expression()?;
                Ok(Expression::UnaryOp(UnaryOp::Not, Box::new(operand)))
            }
            Token::Complement => {
                self.tokiter.next(); // consume
                let operand = self.parse_prefix_expression()?;
                Ok(Expression::UnaryOp(UnaryOp::Complement, Box::new(operand)))
            }
            Token::Increment => {
                self.tokiter.next(); // consume

                let next_loc = self.tokiter.peek().unwrap().location; // for mkperr message
                self.tokiter.reset_peek();

                let operand = self.parse_postfix_expression()?;
                if let Expression::Variable(id) = operand {
                    Ok(Expression::PrefixOp(FixOp::Inc, id))
                } else {
                    Err(ParseError::new(
                        next_loc,
                        "Invalid prefix expression. Expected variable identifier after prefix increment/decrement"
                            .to_string(),
                    ))
                }
            }
            Token::Decrement => {
                self.tokiter.next(); // consume

                let next_loc = self.tokiter.peek().unwrap().location; // for mkperr message
                self.tokiter.reset_peek();

                let operand = self.parse_postfix_expression()?;
                if let Expression::Variable(id) = operand {
                    Ok(Expression::PrefixOp(FixOp::Dec, id))
                } else {
                    Err(ParseError::new(
                        next_loc,
                        "Invalid prefix expression. Expected variable identifier after prefix increment/decrement"
                            .to_string(),
                    ))
                }
            }
            _ => {
                self.tokiter.reset_peek();
                self.parse_postfix_expression()
            }
        }
    }

    fn parse_multiplicative_expression(&mut self) -> Result<Expression, ParseError> {
        let mut factor = self.parse_prefix_expression()?;

        while let Some(tok) = self.tokiter.peek() {
            let optop = match tok.token {
                Token::Multiplication => Some(BinaryOp::Multiplication),
                Token::Division => Some(BinaryOp::Division),
                Token::Remainder => Some(BinaryOp::Remainder),
                _ => None,
            };
            if let Some(op) = optop {
                self.tokiter.next(); // consume
                let next_factor = self.parse_prefix_expression()?;
                factor = Expression::BinaryOp(op, Box::new(factor), Box::new(next_factor));
            } else {
                break;
            }
        }
        self.tokiter.reset_peek();
        Ok(factor)
    }

    fn parse_additive_expression(&mut self) -> Result<Expression, ParseError> {
        let mut term = self.parse_multiplicative_expression()?;

        while let Some(tok) = self.tokiter.peek() {
            let optop = match tok.token {
                Token::Minus => Some(BinaryOp::Subtraction),
                Token::Plus => Some(BinaryOp::Addition),
                _ => None,
            };
            if let Some(op) = optop {
                self.tokiter.next(); // consume
                let next_term = self.parse_multiplicative_expression()?;
                term = Expression::BinaryOp(op, Box::new(term), Box::new(next_term));
            } else {
                break;
            }
        }
        self.tokiter.reset_peek();
        Ok(term)
    }

    fn parse_shift_expression(&mut self) -> Result<Expression, ParseError> {
        let mut adexpr = self.parse_additive_expression()?;

        while let Some(tok) = self.tokiter.peek() {
            let optop = match tok.token {
                Token::LeftShift => Some(BinaryOp::LeftShift),
                Token::RightShift => Some(BinaryOp::RightShift),
                _ => None,
            };
            if let Some(op) = optop {
                self.tokiter.next(); // consume
                let next_adexpr = self.parse_additive_expression()?;
                adexpr = Expression::BinaryOp(op, Box::new(adexpr), Box::new(next_adexpr));
            } else {
                break;
            }
        }
        self.tokiter.reset_peek();
        Ok(adexpr)
    }

    fn parse_relational_expression(&mut self) -> Result<Expression, ParseError> {
        let mut shiftexpr = self.parse_shift_expression()?;

        while let Some(tok) = self.tokiter.peek() {
            let optop = match tok.token {
                Token::Greater => Some(BinaryOp::Greater),
                Token::Less => Some(BinaryOp::Less),
                Token::GreaterEqual => Some(BinaryOp::GreaterEqual),
                Token::LessEqual => Some(BinaryOp::LessEqual),
                _ => None,
            };
            if let Some(op) = optop {
                self.tokiter.next(); // consume
                let next_shiftexpr = self.parse_shift_expression()?;
                shiftexpr = Expression::BinaryOp(op, Box::new(shiftexpr), Box::new(next_shiftexpr));
            } else {
                break;
            }
        }

        self.tokiter.reset_peek();
        Ok(shiftexpr)
    }

    fn parse_equality_expression(&mut self) -> Result<Expression, ParseError> {
        let mut relexpr = self.parse_relational_expression()?;

        while let Some(tok) = self.tokiter.peek() {
            let optop = match tok.token {
                Token::Equal => Some(BinaryOp::Equal),
                Token::NotEqual => Some(BinaryOp::NotEqual),
                _ => None,
            };
            if let Some(op) = optop {
                self.tokiter.next(); // consume
                let next_relexpr = self.parse_relational_expression()?;
                relexpr = Expression::BinaryOp(op, Box::new(relexpr), Box::new(next_relexpr));
            } else {
                break;
            }
        }
        self.tokiter.reset_peek();
        Ok(relexpr)
    }

    fn parse_bitwise_and_expression(&mut self) -> Result<Expression, ParseError> {
        let mut eqexpr = self.parse_equality_expression()?;

        while let Some(tok) = self.tokiter.peek() {
            if let Token::BitwiseAnd = tok.token {
                self.tokiter.next(); // consume
                let next_eqexpr = self.parse_equality_expression()?;
                eqexpr = Expression::BinaryOp(BinaryOp::BitwiseAnd, Box::new(eqexpr), Box::new(next_eqexpr));
            } else {
                break;
            }
        }
        self.tokiter.reset_peek();
        Ok(eqexpr)
    }

    fn parse_bitwise_xor_expression(&mut self) -> Result<Expression, ParseError> {
        let mut bandexpr = self.parse_bitwise_and_expression()?;

        while let Some(tok) = self.tokiter.peek() {
            if let Token::BitwiseXor = tok.token {
                self.tokiter.next(); // consume
                let next_bandexpr = self.parse_bitwise_and_expression()?;
                bandexpr = Expression::BinaryOp(BinaryOp::BitwiseXor, Box::new(bandexpr), Box::new(next_bandexpr));
            } else {
                break;
            }
        }
        self.tokiter.reset_peek();
        Ok(bandexpr)
    }

    fn parse_bitwise_or_expression(&mut self) -> Result<Expression, ParseError> {
        let mut bxorexpr = self.parse_bitwise_xor_expression()?;

        while let Some(tok) = self.tokiter.peek() {
            if let Token::BitwiseOr = tok.token {
                self.tokiter.next(); // consume
                let next_bxorexpr = self.parse_bitwise_xor_expression()?;
                bxorexpr = Expression::BinaryOp(BinaryOp::BitwiseOr, Box::new(bxorexpr), Box::new(next_bxorexpr));
            } else {
                break;
            }
        }
        self.tokiter.reset_peek();
        Ok(bxorexpr)
    }

    fn parse_logical_and_expression(&mut self) -> Result<Expression, ParseError> {
        let mut borexpr = self.parse_bitwise_or_expression()?;

        while let Some(tok) = self.tokiter.peek() {
            if let Token::LogicalAnd = tok.token {
                self.tokiter.next(); // consume
                let next_borexpr = self.parse_bitwise_or_expression()?;
                borexpr = Expression::BinaryOp(BinaryOp::LogicalAnd, Box::new(borexpr), Box::new(next_borexpr));
            } else {
                break;
            }
        }
        self.tokiter.reset_peek();
        Ok(borexpr)
    }

    fn parse_logical_or_expression(&mut self) -> Result<Expression, ParseError> {
        let mut laexpr = self.parse_logical_and_expression()?;

        while let Some(tok) = self.tokiter.peek() {
            if let Token::LogicalOr = tok.token {
                self.tokiter.next(); // consume
                let next_laexpr = self.parse_logical_and_expression()?;
                laexpr = Expression::BinaryOp(BinaryOp::LogicalOr, Box::new(laexpr), Box::new(next_laexpr));
            } else {
                break;
            }
        }
        self.tokiter.reset_peek();
        Ok(laexpr)
    }

    fn parse_conditional_expression(&mut self) -> Result<Expression, ParseError> {
        let loexpr = self.parse_logical_or_expression()?;

        if let Token::QuestionMark = &self.tokiter.peek().unwrap().token {
            self.tokiter.next(); // consume

            let ifexpr = self.parse_expression()?;

            let tok = self.tokiter.next().unwrap();
            if let Token::Colon = tok.token {
            } else {
                return Err(mkperr(tok, "Invalid conditional expression. Expected a colon"));
            }

            let elseexpr = self.parse_conditional_expression()?;

            Ok(Expression::Conditional(Box::new(loexpr), Box::new(ifexpr), Box::new(elseexpr)))
        } else {
            self.tokiter.reset_peek();
            Ok(loexpr)
        }
    }

    fn parse_expression(&mut self) -> Result<Expression, ParseError> {
        if let Token::Identifier(id) = &self.tokiter.peek().unwrap().token {
            let ass = match self.tokiter.peek().unwrap().token {
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
                self.tokiter.next(); // consume twice
                self.tokiter.next();
                let expr = self.parse_expression()?;
                return Ok(Expression::Assign(asskind, id.to_string(), Box::new(expr)));
            }
        }

        self.tokiter.reset_peek();
        self.parse_conditional_expression()
    }

    fn ensure_semicolon(&mut self, msg: &str) -> Result<(), ParseError> {
        // ensure last token is a semicolon
        let tok = self.tokiter.next().unwrap();
        if let Token::Semicolon = tok.token {
            Ok(())
        } else {
            Err(mkperr(tok, &format!("{}. Expected a final semicolon", msg)))
        }
    }

    fn parse_statement(&mut self) -> Result<Statement, ParseError> {
        let stmt = match self.tokiter.peek().unwrap().token {
            Token::Keyword(Keyword::Return) => {
                self.tokiter.next(); // consume
                let expr = self.parse_expression()?;
                self.ensure_semicolon("Invalid return statement")?;
                Statement::Return(expr)
            }
            Token::Keyword(Keyword::If) => {
                self.tokiter.next(); // consume

                // ensure next token is '('
                let mut tok = self.tokiter.next().unwrap();
                if let Token::Lparen = tok.token {
                } else {
                    return Err(mkperr(tok, "Invalid if statement. Expected '('"));
                }

                let cond_expr = self.parse_expression()?;

                // ensure next token is ')'
                tok = self.tokiter.next().unwrap();
                if let Token::Rparen = tok.token {
                } else {
                    return Err(mkperr(tok, "Invalid if statement. Expected ')' after condition expression"));
                }

                let if_stmnt = self.parse_statement()?;

                if let Token::Keyword(Keyword::Else) = self.tokiter.peek().unwrap().token {
                    self.tokiter.next(); // consume

                    let else_stmnt = self.parse_statement()?;

                    Statement::If(cond_expr, Box::new(if_stmnt), Some(Box::new(else_stmnt)))
                } else {
                    self.tokiter.reset_peek();
                    Statement::If(cond_expr, Box::new(if_stmnt), None)
                }
            }
            _ => {
                self.tokiter.reset_peek();
                // then we have an expression to parse
                let expr = self.parse_expression()?;
                self.ensure_semicolon("Invalid expression statement")?;
                Statement::Expr(expr)
            }
        };

        Ok(stmt)
    }

    fn parse_block_item(&mut self) -> Result<BlockItem, ParseError> {
        let bkitem = match self.tokiter.peek().unwrap().token {
            Token::Keyword(Keyword::Int) => {
                self.tokiter.next(); // consume

                let mut tok = self.tokiter.next().unwrap();
                let id = match &tok.token {
                    Token::Identifier(n) => n,
                    _ => {
                        return Err(mkperr(tok, "Invalid declaration. Expected an identifier"));
                    }
                };

                // parse initialization if next token is an assignment (equals sign)
                tok = self.tokiter.peek().unwrap();
                let init = match tok.token {
                    Token::Assignment => {
                        self.tokiter.next(); // consume
                        Some(self.parse_expression()?)
                    }
                    _ => {
                        self.tokiter.reset_peek();
                        None
                    }
                };

                // ensure last token is a semicolon
                self.ensure_semicolon("Invalid declaration")?;

                BlockItem::Decl(id.to_string(), init)
            }
            _ => {
                self.tokiter.reset_peek();
                // then we have an expression to parse
                BlockItem::Stmt(self.parse_statement()?)
            }
        };

        Ok(bkitem)
    }

    fn parse_function(&mut self) -> Result<Function, ParseError> {
        // ensure first token is an Int keyword
        let mut tok = self.tokiter.next().unwrap();

        if let Token::Keyword(Keyword::Int) = tok.token {
        } else {
            return Err(mkperr(tok, "Invalid function definition. Expected return type"));
        }

        // next token should be an identifier
        tok = self.tokiter.next().unwrap();
        let function_name = match &tok.token {
            Token::Identifier(ident) => ident,
            _ => {
                return Err(mkperr(tok, "Invalid function definition. Expected identifier"));
            }
        };

        // ensure next token is '('
        tok = self.tokiter.next().unwrap();
        if let Token::Lparen = tok.token {
        } else {
            return Err(mkperr(tok, "Invalid function definition. Expected '('"));
        }

        // ensure next token is ')'
        tok = self.tokiter.next().unwrap();
        if let Token::Rparen = tok.token {
        } else {
            return Err(mkperr(tok, "Invalid function definition. Expected ')'"));
        }

        // ensure next token is '{'
        tok = self.tokiter.next().unwrap();
        if let Token::Lbrace = tok.token {
        } else {
            let msg = format!("Invalid function definition. Expected '{{', got '{}'.", tok.token);
            return Err(ParseError::new(tok.location, msg));
        }

        // parse statements
        let mut block_items = Vec::new();

        loop {
            tok = self.tokiter.peek().unwrap();
            if let Token::Rbrace = tok.token {
                break;
            }
            self.tokiter.reset_peek();
            block_items.push(self.parse_block_item()?);
        }

        self.tokiter.next(); // consume the Rbrace

        Ok(Function::Func(function_name.to_string(), block_items))
    }

    fn parse_program(&mut self) -> Result<Program, ParseError> {
        Ok(Program::Prog(self.parse_function()?))
    }
}
