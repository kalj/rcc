extern crate itertools;
use crate::tokenizer::{Keyword, TokNLoc, Token};
use core::slice::Iter;
use itertools::MultiPeek;
use std::error;
use std::fmt;

use crate::ast::{AssignmentKind, BinaryOp, FixOp, UnaryOp};
use crate::ast::{BlockItem, CompoundStatement, Declaration, Expression, Function, Program, Statement};

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

fn mkperr(tok: TokNLoc, msg: &str) -> ParseError {
    ParseError { cursor: tok.location, message: format!("{}, got '{}'.", msg, tok.token) }
}

pub struct Parser<'a> {
    tokiter: MultiPeek<Iter<'a, TokNLoc>>,
}

impl Parser<'_> {
    pub fn new(tokens: &[TokNLoc]) -> Parser {
        Parser { tokiter: itertools::multipeek(tokens.iter()) }
    }

    fn next(&mut self) -> Option<TokNLoc> {
        match self.tokiter.next() {
            Some(t) => Some(t.clone()),
            None => None,
        }
    }

    fn peek_n(&mut self, n: u8) -> Option<TokNLoc> {
        let mut p = None;
        for _i in 0..n {
            p = self.tokiter.peek();
        }
        let res = match p {
            Some(t) => Some((*t).clone()),
            None => None,
        };
        self.tokiter.reset_peek();
        res
    }

    fn peek(&mut self) -> Option<TokNLoc> {
        self.peek_n(1)
    }

    pub fn parse(&mut self) -> Result<Program, ParseError> {
        self.parse_program()
    }

    fn parse_postfix_expression(&mut self) -> Result<Expression, ParseError> {
        let tok = self.next().unwrap();
        match tok.token {
            Token::Lparen => {
                let subexpr = self.parse_expression()?;
                let tok = self.next().unwrap();
                match tok.token {
                    Token::Rparen => Ok(subexpr),
                    _ => Err(mkperr(tok, "Missing closing parenthesis after expression")),
                }
            }
            Token::Identifier(id) => {
                match self.peek().unwrap().token {
                    Token::Increment => {
                        self.next(); // consume
                        Ok(Expression::PostfixOp(FixOp::Inc, id))
                    }
                    Token::Decrement => {
                        self.next(); // consume
                        Ok(Expression::PostfixOp(FixOp::Dec, id))
                    }
                    _ => Ok(Expression::Variable(id)),
                }
            }
            Token::IntLiteral(v) => Ok(Expression::Constant(v)),
            _ => Err(mkperr(
                tok,
                "Invalid postfix expression. \
                                 Expected int literal, (expr), or identifier \
                                 possibly with postfix operator",
            )),
        }
    }

    fn parse_prefix_expression(&mut self) -> Result<Expression, ParseError> {
        let tok = self.peek().unwrap();
        match tok.token {
            Token::Minus => {
                self.next(); // consume
                let operand = self.parse_prefix_expression()?;
                Ok(Expression::UnaryOp(UnaryOp::Negate, Box::new(operand)))
            }
            Token::Not => {
                self.next(); // consume
                let operand = self.parse_prefix_expression()?;
                Ok(Expression::UnaryOp(UnaryOp::Not, Box::new(operand)))
            }
            Token::Complement => {
                self.next(); // consume
                let operand = self.parse_prefix_expression()?;
                Ok(Expression::UnaryOp(UnaryOp::Complement, Box::new(operand)))
            }
            Token::Increment => {
                self.next(); // consume

                let next_loc = self.peek().unwrap().location; // for mkperr message

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
                self.next(); // consume

                let next_loc = self.peek().unwrap().location; // for mkperr message

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
            _ => self.parse_postfix_expression(),
        }
    }

    fn parse_multiplicative_expression(&mut self) -> Result<Expression, ParseError> {
        let mut factor = self.parse_prefix_expression()?;

        while let Some(tok) = self.peek() {
            let optop = match tok.token {
                Token::Multiplication => Some(BinaryOp::Multiplication),
                Token::Division => Some(BinaryOp::Division),
                Token::Remainder => Some(BinaryOp::Remainder),
                _ => None,
            };
            if let Some(op) = optop {
                self.next(); // consume
                let next_factor = self.parse_prefix_expression()?;
                factor = Expression::BinaryOp(op, Box::new(factor), Box::new(next_factor));
            } else {
                break;
            }
        }
        Ok(factor)
    }

    fn parse_additive_expression(&mut self) -> Result<Expression, ParseError> {
        let mut term = self.parse_multiplicative_expression()?;

        while let Some(tok) = self.peek() {
            let optop = match tok.token {
                Token::Minus => Some(BinaryOp::Subtraction),
                Token::Plus => Some(BinaryOp::Addition),
                _ => None,
            };
            if let Some(op) = optop {
                self.next(); // consume
                let next_term = self.parse_multiplicative_expression()?;
                term = Expression::BinaryOp(op, Box::new(term), Box::new(next_term));
            } else {
                break;
            }
        }
        Ok(term)
    }

    fn parse_shift_expression(&mut self) -> Result<Expression, ParseError> {
        let mut adexpr = self.parse_additive_expression()?;

        while let Some(tok) = self.peek() {
            let optop = match tok.token {
                Token::LeftShift => Some(BinaryOp::LeftShift),
                Token::RightShift => Some(BinaryOp::RightShift),
                _ => None,
            };
            if let Some(op) = optop {
                self.next(); // consume
                let next_adexpr = self.parse_additive_expression()?;
                adexpr = Expression::BinaryOp(op, Box::new(adexpr), Box::new(next_adexpr));
            } else {
                break;
            }
        }
        Ok(adexpr)
    }

    fn parse_relational_expression(&mut self) -> Result<Expression, ParseError> {
        let mut shiftexpr = self.parse_shift_expression()?;

        while let Some(tok) = self.peek() {
            let optop = match tok.token {
                Token::Greater => Some(BinaryOp::Greater),
                Token::Less => Some(BinaryOp::Less),
                Token::GreaterEqual => Some(BinaryOp::GreaterEqual),
                Token::LessEqual => Some(BinaryOp::LessEqual),
                _ => None,
            };
            if let Some(op) = optop {
                self.next(); // consume
                let next_shiftexpr = self.parse_shift_expression()?;
                shiftexpr = Expression::BinaryOp(op, Box::new(shiftexpr), Box::new(next_shiftexpr));
            } else {
                break;
            }
        }

        Ok(shiftexpr)
    }

    fn parse_equality_expression(&mut self) -> Result<Expression, ParseError> {
        let mut relexpr = self.parse_relational_expression()?;

        while let Some(tok) = self.peek() {
            let optop = match tok.token {
                Token::Equal => Some(BinaryOp::Equal),
                Token::NotEqual => Some(BinaryOp::NotEqual),
                _ => None,
            };
            if let Some(op) = optop {
                self.next(); // consume
                let next_relexpr = self.parse_relational_expression()?;
                relexpr = Expression::BinaryOp(op, Box::new(relexpr), Box::new(next_relexpr));
            } else {
                break;
            }
        }
        Ok(relexpr)
    }

    fn parse_bitwise_and_expression(&mut self) -> Result<Expression, ParseError> {
        let mut eqexpr = self.parse_equality_expression()?;

        while let Some(tok) = self.peek() {
            if let Token::BitwiseAnd = tok.token {
                self.next(); // consume
                let next_eqexpr = self.parse_equality_expression()?;
                eqexpr = Expression::BinaryOp(BinaryOp::BitwiseAnd, Box::new(eqexpr), Box::new(next_eqexpr));
            } else {
                break;
            }
        }
        Ok(eqexpr)
    }

    fn parse_bitwise_xor_expression(&mut self) -> Result<Expression, ParseError> {
        let mut bandexpr = self.parse_bitwise_and_expression()?;

        while let Some(tok) = self.peek() {
            if let Token::BitwiseXor = tok.token {
                self.next(); // consume
                let next_bandexpr = self.parse_bitwise_and_expression()?;
                bandexpr = Expression::BinaryOp(BinaryOp::BitwiseXor, Box::new(bandexpr), Box::new(next_bandexpr));
            } else {
                break;
            }
        }
        Ok(bandexpr)
    }

    fn parse_bitwise_or_expression(&mut self) -> Result<Expression, ParseError> {
        let mut bxorexpr = self.parse_bitwise_xor_expression()?;

        while let Some(tok) = self.peek() {
            if let Token::BitwiseOr = tok.token {
                self.next(); // consume
                let next_bxorexpr = self.parse_bitwise_xor_expression()?;
                bxorexpr = Expression::BinaryOp(BinaryOp::BitwiseOr, Box::new(bxorexpr), Box::new(next_bxorexpr));
            } else {
                break;
            }
        }
        Ok(bxorexpr)
    }

    fn parse_logical_and_expression(&mut self) -> Result<Expression, ParseError> {
        let mut borexpr = self.parse_bitwise_or_expression()?;

        while let Some(tok) = self.peek() {
            if let Token::LogicalAnd = tok.token {
                self.next(); // consume
                let next_borexpr = self.parse_bitwise_or_expression()?;
                borexpr = Expression::BinaryOp(BinaryOp::LogicalAnd, Box::new(borexpr), Box::new(next_borexpr));
            } else {
                break;
            }
        }
        Ok(borexpr)
    }

    fn parse_logical_or_expression(&mut self) -> Result<Expression, ParseError> {
        let mut laexpr = self.parse_logical_and_expression()?;

        while let Some(tok) = self.peek() {
            if let Token::LogicalOr = tok.token {
                self.next(); // consume
                let next_laexpr = self.parse_logical_and_expression()?;
                laexpr = Expression::BinaryOp(BinaryOp::LogicalOr, Box::new(laexpr), Box::new(next_laexpr));
            } else {
                break;
            }
        }
        Ok(laexpr)
    }

    fn parse_conditional_expression(&mut self) -> Result<Expression, ParseError> {
        let loexpr = self.parse_logical_or_expression()?;

        if let Token::QuestionMark = &self.peek().unwrap().token {
            self.next(); // consume

            let ifexpr = self.parse_expression()?;

            let tok = self.next().unwrap();
            if let Token::Colon = tok.token {
            } else {
                return Err(mkperr(tok, "Invalid conditional expression. Expected a colon"));
            }

            let elseexpr = self.parse_conditional_expression()?;

            Ok(Expression::Conditional(Box::new(loexpr), Box::new(ifexpr), Box::new(elseexpr)))
        } else {
            Ok(loexpr)
        }
    }

    fn parse_expression(&mut self) -> Result<Expression, ParseError> {
        if let Token::Identifier(id) = &self.peek().unwrap().token {
            let ass = match self.peek_n(2).unwrap().token {
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
                self.next(); // consume twice
                self.next();
                let expr = self.parse_expression()?;
                return Ok(Expression::Assign(asskind, id.to_string(), Box::new(expr)));
            }
        }

        self.parse_conditional_expression()
    }

    fn ensure_semicolon(&mut self, msg: &str) -> Result<(), ParseError> {
        // ensure last token is a semicolon
        let tok = self.next().unwrap();
        if let Token::Semicolon = tok.token {
            Ok(())
        } else {
            Err(mkperr(tok, &format!("{}. Expected a final semicolon", msg)))
        }
    }

    fn parse_compound_statement(&mut self) -> Result<CompoundStatement, ParseError> {
        // ensure next token is '{'
        let tok = self.next().unwrap();
        if let Token::Lbrace = tok.token {
        } else {
            return Err(mkperr(tok, "Invalid compound statement. Expected '{{'"));
        }

        // parse block items
        let mut block_items = Vec::new();

        loop {
            if let Token::Rbrace = self.peek().unwrap().token {
                break;
            }
            block_items.push(self.parse_block_item()?);
        }

        // we know next token is '}'
        // simply consume
        self.next(); // consume
        // return Err(mkperr(tok, "Invalid compound statement. Expected '}}'"));

        Ok(CompoundStatement { block_items })
    }

    fn parse_statement(&mut self) -> Result<Statement, ParseError> {
        let stmt = match self.peek().unwrap().token {
            Token::Lbrace => {
                let comp = self.parse_compound_statement()?;
                Statement::Compound(comp)
            }
            Token::Keyword(Keyword::Return) => {
                self.next(); // consume
                let expr = self.parse_expression()?;
                self.ensure_semicolon("Invalid return statement")?;
                Statement::Return(expr)
            }
            Token::Keyword(Keyword::Continue) => {
                self.next(); // consume
                self.ensure_semicolon("Invalid continue statement")?;
                Statement::Continue
            }
            Token::Keyword(Keyword::Break) => {
                self.next(); // consume
                self.ensure_semicolon("Invalid break statement")?;
                Statement::Break
            }
            Token::Keyword(Keyword::If) => {
                self.next(); // consume

                // ensure next token is '('
                let mut tok = self.next().unwrap();
                if let Token::Lparen = tok.token {
                } else {
                    return Err(mkperr(tok, "Invalid if statement. Expected '('"));
                }

                let cond_expr = self.parse_expression()?;

                // ensure next token is ')'
                tok = self.next().unwrap();
                if let Token::Rparen = tok.token {
                } else {
                    return Err(mkperr(tok, "Invalid if statement. Expected ')' after condition expression"));
                }

                let if_stmnt = self.parse_statement()?;

                if let Token::Keyword(Keyword::Else) = self.peek().unwrap().token {
                    self.next(); // consume

                    let else_stmnt = self.parse_statement()?;

                    Statement::If(cond_expr, Box::new(if_stmnt), Some(Box::new(else_stmnt)))
                } else {
                    Statement::If(cond_expr, Box::new(if_stmnt), None)
                }
            }
            Token::Keyword(Keyword::While) => {
                self.next(); // consume

                // ensure next token is '('
                let mut tok = self.next().unwrap();
                if let Token::Lparen = tok.token {
                } else {
                    return Err(mkperr(tok, "Invalid while statement. Expected '('"));
                }

                let cond_expr = self.parse_expression()?;

                // ensure next token is ')'
                tok = self.next().unwrap();
                if let Token::Rparen = tok.token {
                } else {
                    return Err(mkperr(tok, "Invalid while statement. Expected ')' after condition expression"));
                }

                let body = self.parse_statement()?;

                Statement::While(cond_expr, Box::new(body))
            }
            Token::Keyword(Keyword::Do) => {
                self.next(); // consume

                let body = self.parse_statement()?;

                // ensure next token is 'while'
                let mut tok = self.next().unwrap();
                if let Token::Keyword(Keyword::While) = tok.token {
                } else {
                    return Err(mkperr(tok, "Invalid do-while statement. Expected 'while'"));
                }

                // ensure next token is '('
                tok = self.next().unwrap();
                if let Token::Lparen = tok.token {
                } else {
                    return Err(mkperr(tok, "Invalid do-while statement. Expected '('"));
                }

                let cond_expr = self.parse_expression()?;

                // ensure next token is ')'
                tok = self.next().unwrap();
                if let Token::Rparen = tok.token {
                } else {
                    return Err(mkperr(tok, "Invalid do-while statement. Expected ')' after condition expression"));
                }

                self.ensure_semicolon("Invalid do-while statement")?;

                Statement::DoWhile(Box::new(body), cond_expr)
            }
            Token::Keyword(Keyword::For) => {
                self.next(); // consume

                // ensure next token is '('
                let mut tok = self.next().unwrap();
                if let Token::Lparen = tok.token {
                } else {
                    return Err(mkperr(tok, "Invalid For/ForDecl statement. Expected '('"));
                }

                let mut init_decl: Option<Declaration> = None;
                let mut init_expr: Option<Expression> = None;

                tok = self.peek().unwrap();
                match tok.token {
                    Token::Keyword(Keyword::Int) => {
                        init_decl = Some(self.parse_declaration()?);
                        // no need to look for ';', it is included in declaration
                    }
                    Token::Semicolon => {
                        self.next(); // consume
                    }
                    _ => {
                        init_expr = Some(self.parse_expression()?);
                        self.ensure_semicolon("Invalid initialization expression for For statement")?;
                    }
                }

                let cond_expr = if let Token::Semicolon = self.peek().unwrap().token {
                    // no conditional expression - generate a constant '1'
                    Expression::Constant(1)
                } else {
                    self.parse_expression()?
                };

                self.ensure_semicolon("Invalid condition expression for ForDecl statement")?;

                let post_expr = if let Token::Rparen = self.peek().unwrap().token {
                    // no post_expr, Rparen read below
                    None
                } else {
                    let pexpr = self.parse_expression()?;
                    Some(pexpr)
                };

                // ensure next token is ')'
                let tok = self.next().unwrap();
                if let Token::Rparen = tok.token {
                } else {
                    return Err(mkperr(tok, "Invalid forDecl statement. Expected ')' after post expression"));
                }

                let body = self.parse_statement()?;

                if let Some(decl) = init_decl {
                    Statement::ForDecl(decl, cond_expr, post_expr, Box::new(body))
                } else {
                    Statement::For(init_expr, cond_expr, post_expr, Box::new(body))
                }
            }
            _ => {
                // then we have an expression to parse

                if let Token::Semicolon = self.peek().unwrap().token {
                    self.tokiter.next(); // consume
                    Statement::Null
                } else {
                    let expr = self.parse_expression()?;
                    self.ensure_semicolon("Invalid expression statement")?;
                    Statement::Expr(expr)
                }
            }
        };

        Ok(stmt)
    }

    fn parse_declaration(&mut self) -> Result<Declaration, ParseError> {
        // ensure we got a type (i.e. 'int')
        let tok = self.next().unwrap();
        if let Token::Keyword(Keyword::Int) = tok.token {
        } else {
            return Err(mkperr(tok, "Invalid declaration. Expected type specifier"));
        }

        let mut tok = self.next().unwrap();
        let id = match tok.token {
            Token::Identifier(n) => n,
            _ => {
                return Err(mkperr(tok, "Invalid declaration. Expected an identifier"));
            }
        };

        // parse initialization if next token is an assignment (equals sign)
        tok = self.peek().unwrap();
        let init = match tok.token {
            Token::Assignment => {
                self.next(); // consume
                Some(self.parse_expression()?)
            }
            _ => None,
        };

        // ensure last token is a semicolon
        self.ensure_semicolon("Invalid declaration")?;

        Ok(Declaration { id, init })
    }

    fn parse_block_item(&mut self) -> Result<BlockItem, ParseError> {
        let bkitem = match self.peek().unwrap().token {
            Token::Keyword(Keyword::Int) => {
                let declaration = self.parse_declaration()?;

                BlockItem::Decl(declaration)
            }
            _ => {
                // then we have an expression to parse
                BlockItem::Stmt(self.parse_statement()?)
            }
        };

        Ok(bkitem)
    }

    fn parse_function(&mut self) -> Result<Function, ParseError> {
        // ensure first token is an Int keyword
        let mut tok = self.next().unwrap();

        if let Token::Keyword(Keyword::Int) = tok.token {
        } else {
            return Err(mkperr(tok, "Invalid function definition. Expected return type"));
        }

        // next token should be an identifier
        tok = self.next().unwrap();
        let function_name = match tok.token {
            Token::Identifier(ident) => ident,
            _ => {
                return Err(mkperr(tok, "Invalid function definition. Expected identifier"));
            }
        };

        // ensure next token is '('
        tok = self.next().unwrap();
        if let Token::Lparen = tok.token {
        } else {
            return Err(mkperr(tok, "Invalid function definition. Expected '('"));
        }

        // ensure next token is ')'
        tok = self.next().unwrap();
        if let Token::Rparen = tok.token {
        } else {
            return Err(mkperr(tok, "Invalid function definition. Expected ')'"));
        }

        // parse body
        let body = self.parse_compound_statement()?;

        // ensure next token is '{'
        // return Err(mkperr(tok, "Invalid function definition. Expected '{{'"));

        // // ensure next token is '}'
        //     return Err(mkperr(tok, "Invalid function definition. Expected '}}'"));

        Ok(Function::Func(function_name, body))
    }

    fn parse_program(&mut self) -> Result<Program, ParseError> {
        let main = self.parse_function()?;

        if let Some(t) = self.next() {
            Err(mkperr(t, "Stray token at end of program"))
        } else {
            Ok(Program::Prog(main))
        }
    }
}
