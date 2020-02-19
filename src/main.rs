extern crate clap;
extern crate regex;
use clap::{App, Arg};
use core::slice::Iter;
use regex::Regex;
use std::error;
use std::fmt;
use std::fs;
use std::iter::Peekable;
use std::path::{Path, PathBuf};

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
    Not,
    Complement,
    Keyword(Keyword),
    Identifier(String),
    IntLiteral(i64),
}

fn token_to_str(tok: &Token) -> String {
    match tok {
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
        Token::Not => "!".to_string(),
        Token::Complement => "~".to_string(),
        Token::Keyword(kw) => match kw {
            Keyword::Int => "int".to_string(),
            Keyword::Return => "return".to_string(),
        },
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

fn get_token_pattern(tok: &Token) -> &str {
    match tok {
        Token::Lparen => r"^\(",
        Token::Rparen => r"^\)",
        Token::Lbrace => r"^\{",
        Token::Rbrace => r"^\}",
        Token::Semicolon => r"^;",
        Token::Multiplication => r"^\*",
        Token::Division => r"^/",
        Token::Remainder => r"^%",
        Token::Plus => r"^\+",
        Token::Minus => r"^-",
        Token::LogicalAnd => r"^&&",
        Token::LogicalOr => r"^\|\|",
        Token::Equal => r"^==",
        Token::NotEqual => r"^!=",
        Token::LessEqual => r"^<=",
        Token::GreaterEqual => r"^>=",
        Token::Less => r"^<",
        Token::Greater => r"^>",
        Token::BitwiseAnd => r"^&",
        Token::BitwiseOr => r"^\|",
        Token::BitwiseXor => r"^\^",
        Token::Not => r"^!",
        Token::Complement => r"^~",
        Token::Keyword(kw) => match kw {
            Keyword::Int => r"^int\W",
            Keyword::Return => r"^return\W",
        },
        Token::Identifier(_) => r"([a-zA-Z]\w*)",
        Token::IntLiteral(_) => r"([0-9]+)",
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
        Token::LogicalAnd,
        Token::LogicalOr,
        Token::BitwiseAnd,
        Token::BitwiseOr,
        Token::BitwiseXor,
        Token::Equal,
        Token::NotEqual,
        Token::LessEqual,
        Token::GreaterEqual,
        Token::Less,
        Token::Greater,
        Token::Not,
        Token::Complement,
        Token::Keyword(Keyword::Int),
        Token::Keyword(Keyword::Return),
        Token::Identifier("a".to_string()),
        Token::IntLiteral(1),
    ];

    for t in toktypes.iter() {
        let re = Regex::new(get_token_pattern(t)).expect(&format!(
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
                Token::Keyword(kw) => Ok(Token::Keyword(*kw)),
                _ => Ok(t.clone()),
            };
        }
    }
    return Err(TokenError { cursor: cursor });
}

fn tokenize(source: &str) -> Vec<Token> {
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
        cursor += token_length(&tok);
        result.push(tok);
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
}

#[derive(Debug)]
enum UnaryOp {
    Negate,
    Not,
    Complement,
}

#[derive(Debug)]
enum Expression {
    BinaryOp(BinaryOp, Box<Expression>, Box<Expression>),
    UnaryOp(UnaryOp, Box<Expression>),
    Constant(i64),
}

#[derive(Debug)]
enum Statement {
    Return(Expression),
}

#[derive(Debug)]
enum FunctionDeclaration {
    Function(String, Statement),
}

#[derive(Debug)]
enum Program {
    Program(FunctionDeclaration),
}

fn print_expression(expr: &Expression, lvl: i32) {
    match expr {
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
        Expression::Constant(val) => {
            println!("{0:<1$}Constant {2}", "", (lvl * 2) as usize, val);
        }
    }
}

fn print_statement(stmt: &Statement, lvl: i32) {
    let Statement::Return(expr) = stmt;

    println!("{: <1$}Return {{", "", (lvl * 2) as usize);
    print_expression(expr, lvl + 1);
    println!("{: <1$}}}", "", (lvl * 2) as usize);
}

fn print_program(prog: &Program) {
    let lvl = 0;
    println!("Program {{");
    let Program::Program(FunctionDeclaration::Function(name, stmt)) = prog;
    println!("  Function \"{}\" {{", name);
    print_statement(stmt, lvl + 2);
    println!("  }}");
    println!("}}");
}

//===================================================================
// Parsing
//===================================================================

fn parse_factor(tokiter: &mut Peekable<Iter<Token>>) -> Expression {
    let mut tok = tokiter.next().unwrap();
    match tok {
        Token::Lparen => {
            let subexpr = parse_expression(tokiter);
            tok = tokiter.next().unwrap();
            if let Token::Rparen = tok {
                subexpr
            } else {
                panic!(
                    "Missing closing parenthesis after expression, got '{}'.",
                    tok
                )
            }
        }
        Token::IntLiteral(v) => Expression::Constant(*v),
        Token::Minus => Expression::UnaryOp(UnaryOp::Negate, Box::new(parse_factor(tokiter))),
        Token::Not => Expression::UnaryOp(UnaryOp::Not, Box::new(parse_factor(tokiter))),
        Token::Complement => {
            Expression::UnaryOp(UnaryOp::Complement, Box::new(parse_factor(tokiter)))
        }
        _ => panic!(
            "Invalid token for factor. Expected '(', '-', '!', '~', or an int literal, got '{}'.",
            tok
        ),
    }
}

fn parse_term(tokiter: &mut Peekable<Iter<Token>>) -> Expression {
    let mut factor = parse_factor(tokiter);
    while let Some(tok) = tokiter.peek() {
        let optop = match tok {
            Token::Multiplication => Some(BinaryOp::Multiplication),
            Token::Division => Some(BinaryOp::Division),
            Token::Remainder => Some(BinaryOp::Remainder),
            _ => None,
        };
        if let Some(op) = optop {
            tokiter.next(); // consume
            let next_factor = parse_factor(tokiter);
            factor = Expression::BinaryOp(op, Box::new(factor), Box::new(next_factor));
        } else {
            break;
        }
    }
    return factor;
}

fn parse_additive_expression(tokiter: &mut Peekable<Iter<Token>>) -> Expression {
    let mut term = parse_term(tokiter);
    while let Some(tok) = tokiter.peek() {
        let optop = match tok {
            Token::Minus => Some(BinaryOp::Subtraction),
            Token::Plus => Some(BinaryOp::Addition),
            _ => None,
        };
        if let Some(op) = optop {
            tokiter.next(); // consume
            let next_term = parse_term(tokiter);
            term = Expression::BinaryOp(op, Box::new(term), Box::new(next_term));
        } else {
            break;
        }
    }
    return term;
}

fn parse_relational_expression(tokiter: &mut Peekable<Iter<Token>>) -> Expression {
    let mut adexpr = parse_additive_expression(tokiter);
    while let Some(tok) = tokiter.peek() {
        let optop = match tok {
            Token::Greater => Some(BinaryOp::Greater),
            Token::Less => Some(BinaryOp::Less),
            Token::GreaterEqual => Some(BinaryOp::GreaterEqual),
            Token::LessEqual => Some(BinaryOp::LessEqual),
            _ => None,
        };
        if let Some(op) = optop {
            tokiter.next(); // consume
            let next_adexpr = parse_additive_expression(tokiter);
            adexpr = Expression::BinaryOp(op, Box::new(adexpr), Box::new(next_adexpr));
        } else {
            break;
        }
    }
    return adexpr;
}

fn parse_equality_expression(tokiter: &mut Peekable<Iter<Token>>) -> Expression {
    let mut relexpr = parse_relational_expression(tokiter);
    while let Some(tok) = tokiter.peek() {
        let optop = match tok {
            Token::Equal => Some(BinaryOp::Equal),
            Token::NotEqual => Some(BinaryOp::NotEqual),
            _ => None,
        };
        if let Some(op) = optop {
            tokiter.next(); // consume
            let next_relexpr = parse_relational_expression(tokiter);
            relexpr = Expression::BinaryOp(op, Box::new(relexpr), Box::new(next_relexpr));
        } else {
            break;
        }
    }
    return relexpr;
}

fn parse_bitwise_and_expression(tokiter: &mut Peekable<Iter<Token>>) -> Expression {
    let mut eqexpr = parse_equality_expression(tokiter);
    while let Some(tok) = tokiter.peek() {
        match tok {
            Token::BitwiseAnd => {
                tokiter.next(); // consume
                let next_eqexpr = parse_equality_expression(tokiter);
                eqexpr = Expression::BinaryOp(
                    BinaryOp::BitwiseAnd,
                    Box::new(eqexpr),
                    Box::new(next_eqexpr),
                );
            }
            _ => {
                break;
            }
        }
    }
    return eqexpr;
}

fn parse_bitwise_xor_expression(tokiter: &mut Peekable<Iter<Token>>) -> Expression {
    let mut bandexpr = parse_bitwise_and_expression(tokiter);
    while let Some(tok) = tokiter.peek() {
        match tok {
            Token::BitwiseXor => {
                tokiter.next(); // consume
                let next_bandexpr = parse_bitwise_and_expression(tokiter);
                bandexpr = Expression::BinaryOp(
                    BinaryOp::BitwiseXor,
                    Box::new(bandexpr),
                    Box::new(next_bandexpr),
                );
            }
            _ => {
                break;
            }
        }
    }
    return bandexpr;
}

fn parse_bitwise_or_expression(tokiter: &mut Peekable<Iter<Token>>) -> Expression {
    let mut bxorexpr = parse_bitwise_xor_expression(tokiter);
    while let Some(tok) = tokiter.peek() {
        match tok {
            Token::BitwiseOr => {
                tokiter.next(); // consume
                let next_bxorexpr = parse_bitwise_xor_expression(tokiter);
                bxorexpr = Expression::BinaryOp(
                    BinaryOp::BitwiseOr,
                    Box::new(bxorexpr),
                    Box::new(next_bxorexpr),
                );
            }
            _ => {
                break;
            }
        }
    }
    return bxorexpr;
}

fn parse_logical_and_expression(tokiter: &mut Peekable<Iter<Token>>) -> Expression {
    let mut borexpr = parse_bitwise_or_expression(tokiter);
    while let Some(tok) = tokiter.peek() {
        match tok {
            Token::LogicalAnd => {
                tokiter.next(); // consume
                let next_borexpr = parse_bitwise_or_expression(tokiter);
                borexpr = Expression::BinaryOp(
                    BinaryOp::LogicalAnd,
                    Box::new(borexpr),
                    Box::new(next_borexpr),
                );
            }
            _ => {
                break;
            }
        }
    }
    return borexpr;
}

fn parse_logical_or_expression(tokiter: &mut Peekable<Iter<Token>>) -> Expression {
    let mut laexpr = parse_logical_and_expression(tokiter);
    while let Some(tok) = tokiter.peek() {
        match tok {
            Token::LogicalOr => {
                tokiter.next(); // consume
                let next_laexpr = parse_logical_and_expression(tokiter);
                laexpr = Expression::BinaryOp(
                    BinaryOp::LogicalOr,
                    Box::new(laexpr),
                    Box::new(next_laexpr),
                );
            }
            _ => {
                break;
            }
        }
    }
    return laexpr;
}

fn parse_expression(tokiter: &mut Peekable<Iter<Token>>) -> Expression {
    parse_logical_or_expression(tokiter)
}

fn parse_statement(tokiter: &mut Peekable<Iter<Token>>) -> Statement {
    // ensure first token is a Return keyword
    let mut tok = tokiter.next().unwrap();
    match tok {
        Token::Keyword(Keyword::Return) => (),
        _ => panic!(
            "Invalid statement. Expected 'return' keyword, got '{}'.",
            tok
        ),
    }

    let expression = parse_expression(tokiter);

    // ensure last token is a semicolon
    tok = tokiter.next().unwrap();
    match tok {
        Token::Semicolon => (),
        _ => panic!(
            "Invalid statement. Expected a final semicolon, got '{}'.",
            tok
        ),
    }

    return Statement::Return(expression);
}

fn parse_function(tokiter: &mut Peekable<Iter<Token>>) -> FunctionDeclaration {
    // ensure first token is an Int keyword
    let mut tok = tokiter.next().unwrap();
    match tok {
        Token::Keyword(Keyword::Int) => (),
        _ => panic!(
            "Invalid function declaration. Expected return type, got '{}'.",
            tok
        ),
    }

    // next token should be an identifier
    tok = tokiter.next().unwrap();
    let function_name = match tok {
        Token::Identifier(ident) => ident,
        _ => panic!(
            "Invalid function declaration. Expected identifier, got '{}'.",
            tok
        ),
    };

    // ensure next token is '('
    tok = tokiter.next().unwrap();
    match tok {
        Token::Lparen => (),
        _ => panic!("Invalid function declaration. Expected '(', got '{}'.", tok),
    }

    // ensure next token is ')'
    tok = tokiter.next().unwrap();
    match tok {
        Token::Rparen => (),
        _ => panic!("Invalid function declaration. Expected ')', got '{}'.", tok),
    }

    // ensure next token is '{'
    tok = tokiter.next().unwrap();
    match tok {
        Token::Lbrace => (),
        _ => panic!(
            "Invalid function declaration. Expected '{{', got '{}'.",
            tok
        ),
    }

    // parse statement
    let statement = parse_statement(tokiter);

    // ensure next token is '}'
    tok = tokiter.next().unwrap();
    match tok {
        Token::Rbrace => (),
        _ => panic!(
            "Invalid function declaration. Expected '}}', got '{}'.",
            tok
        ),
    }

    return FunctionDeclaration::Function(function_name.to_string(), statement);
}

fn parse_program(tokiter: &mut Peekable<Iter<Token>>) -> Program {
    return Program::Program(parse_function(tokiter));
}

fn parse(tokens: &[Token]) -> Program {
    let mut tokiter = tokens.iter().peekable();
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
    rega32: String,
    regc32: String,
    regd32: String,
}

impl Generator {
    fn new(emit_32bit: bool) -> Generator {
        Generator {
            emit_32bit: emit_32bit,
            label_counter: 0,
            rega: (if emit_32bit { "%eax" } else { "%rax" }).to_string(),
            regc: (if emit_32bit { "%ecx" } else { "%rcx" }).to_string(),
            rega32: "%eax".to_string(),
            regc32: "%ecx".to_string(),
            regd32: "%edx".to_string(),
        }
    }

    fn generate_expression_code(&mut self, expr: &Expression) -> Code {
        let mut code = Code::new();
        match expr {
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
                match bop {
                    BinaryOp::Addition => {
                        code.push(CodeLine::i2("pop", &self.regc)); //                   get arg1 from stack
                        code.push(CodeLine::i3("add", &self.regc32, &self.rega32)); //   add, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
                    }
                    BinaryOp::Subtraction => {
                        code.push(CodeLine::i3("mov", &self.rega32, &self.regc32)); //   copy arg2 into %ecx
                        code.push(CodeLine::i2("pop", &self.rega)); //                   get arg1 from stack into %eax
                        code.push(CodeLine::i3("sub", &self.regc32, &self.rega32)); //   subtract %eax (arg1) - %ecx (arg2) -> %eax
                    }
                    BinaryOp::Multiplication => {
                        code.push(CodeLine::i2("pop", &self.regc)); //                   get arg1 from stack
                        code.push(CodeLine::i3("imul", &self.regc32, &self.rega32));
                        // add, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
                    }
                    BinaryOp::Division => {
                        code.push(CodeLine::i3("mov", &self.rega32, &self.regc32)); //   copy arg2 into %ecx
                        code.push(CodeLine::i2("pop", &self.rega)); //                   restore first operand into %eax
                        code.push(CodeLine::i1("cltd")); //                              sign extend %eax into %edx:%eax
                        code.push(CodeLine::i2("idiv", &self.regc32)); //                idiv takes numerator in %eax, denominator in arg (%ecx). quotient is put in %eax, remainder in %edx.
                    }
                    BinaryOp::Remainder => {
                        code.push(CodeLine::i3("mov", &self.rega32, &self.regc32)); //   copy arg2 into %ecx
                        code.push(CodeLine::i2("pop", &self.rega)); //                   restore first operand into %eax
                        code.push(CodeLine::i1("cltd")); //                              sign extend %eax into %edx:%eax
                        code.push(CodeLine::i2("idiv", &self.regc32)); //                idiv takes numerator in %eax, denominator in arg (%ecx). quotient is put in %eax, remainder in %edx.
                        code.push(CodeLine::i3("mov", &self.regd32, &self.rega32)); //   copy result into %eax
                    }
                    BinaryOp::Equal => {
                        code.push(CodeLine::i2("pop", &self.regc)); //                    pop op1 from stack
                        code.push(CodeLine::i3("cmp", &self.regc32, &self.rega32)); //    set ZF if EAX == ECX
                        code.push(CodeLine::i3("mov", "$0", &self.rega32)); //            zero out EAX without changing ZF
                        code.push(CodeLine::i2("sete", "%al")); //                        set bit to 1 if ecx (op1) was equal to eax (op2)
                    }
                    BinaryOp::NotEqual => {
                        code.push(CodeLine::i2("pop", &self.regc)); //                    pop op1 from stack
                        code.push(CodeLine::i3("cmp", &self.regc32, &self.rega32)); //    set ZF if EAX == ECX
                        code.push(CodeLine::i3("mov", "$0", &self.rega32)); //            zero out EAX without changing ZF
                        code.push(CodeLine::i2("setne", "%al")); //                       set bit to 1 if ecx (op1) was not equal to eax (op2)
                    }
                    BinaryOp::Less => {
                        code.push(CodeLine::i2("pop", &self.regc)); //                    pop op1 from stack
                        code.push(CodeLine::i3("cmp", &self.rega32, &self.regc32)); //    compare ECX and EAX
                        code.push(CodeLine::i3("mov", "$0", &self.rega32)); //            zero out EAX without changing ZF
                        code.push(CodeLine::i2("setl", "%al")); //                        set bit to 1 if ecx (op1) was less than eax (op2)
                    }
                    BinaryOp::Greater => {
                        code.push(CodeLine::i2("pop", &self.regc)); //                    pop op1 from stack
                        code.push(CodeLine::i3("cmp", &self.rega32, &self.regc32)); //    compare ECX and EAX
                        code.push(CodeLine::i3("mov", "$0", &self.rega32)); //            zero out EAX without changing ZF
                        code.push(CodeLine::i2("setg", "%al")); //                        set bit to 1 if ecx (op1) was greater than eax (op2)
                    }
                    BinaryOp::LessEqual => {
                        code.push(CodeLine::i2("pop", &self.regc)); //                    pop op1 from stack
                        code.push(CodeLine::i3("cmp", &self.rega32, &self.regc32)); //    compare ECX and EAX
                        code.push(CodeLine::i3("mov", "$0", &self.rega32)); //            zero out EAX without changing ZF
                        code.push(CodeLine::i2("setle", "%al")); //                       set bit to 1 if ecx (op1) was less than or equal to eax (op2)
                    }
                    BinaryOp::GreaterEqual => {
                        code.push(CodeLine::i2("pop", &self.regc)); //                    pop op1 from stack
                        code.push(CodeLine::i3("cmp", &self.rega32, &self.regc32)); //    compare ECX and EAX
                        code.push(CodeLine::i3("mov", "$0", &self.rega32)); //            zero out EAX without changing ZF
                        code.push(CodeLine::i2("setge", "%al")); //                       set bit to 1 if ecx (op1) was greater than or equal to eax (op2)
                    }
                    BinaryOp::BitwiseOr => {
                        code.push(CodeLine::i2("pop", &self.regc)); //                   get arg1 from stack
                        code.push(CodeLine::i3("or", &self.regc32, &self.rega32)); //    and, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
                    }
                    BinaryOp::BitwiseXor => {
                        code.push(CodeLine::i2("pop", &self.regc)); //                   get arg1 from stack
                        code.push(CodeLine::i3("xor", &self.regc32, &self.rega32)); //   and, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
                    }
                    BinaryOp::BitwiseAnd => {
                        code.push(CodeLine::i2("pop", &self.regc)); //                   get arg1 from stack
                        code.push(CodeLine::i3("and", &self.regc32, &self.rega32)); //   and, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
                    }
                    BinaryOp::LogicalAnd | BinaryOp::LogicalOr => {
                        panic!("Internal Error"); // Handled above separately
                    }
                }
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
            Expression::Constant(val) => {
                let literal = format!("${}", val);
                code.push(CodeLine::i3("mov", &literal, &self.rega32));
            }
        }
        return code;
    }

    fn generate_statement_code(&mut self, stmnt: Statement) -> Code {
        let mut code; // = Vec::new();
        match stmnt {
            Statement::Return(expr) => {
                code = self.generate_expression_code(&expr);
                code.push(CodeLine::i1("ret"));
            }
        }
        return code;
    }

    fn generate_program_code(&mut self, prog: Program) -> Code {
        let mut code = Code::new();
        match prog {
            Program::Program(FunctionDeclaration::Function(name, body)) => {
                code.push(CodeLine::i2(".globl", &name));
                code.push(CodeLine::lbl(&name));
                code.append(self.generate_statement_code(body));
            }
        }
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
        let tokenstrs: Vec<String> = tokens.iter().map(|t| format!("{}", t)).collect();
        println!("{}", tokenstrs.join(" "));
    }

    let program = parse(&tokens);

    if verbose {
        println!("After parsing:");
        print_program(&program);
    }

    let mut generator = Generator::new(emit_32bit);
    let assembly_code = generator.generate_program_code(program);

    fs::write(output_path, assembly_code.get_str()).expect("Failed writing assembly output");
}
