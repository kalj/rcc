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
    Plus,
    Minus,
    Not,
    Complement,
    Keyword(Keyword),
    Identifier(String),
    IntLiteral(i64),
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match self {
            Token::Lparen => "(".to_string(),
            Token::Rparen => ")".to_string(),
            Token::Lbrace => "{".to_string(),
            Token::Rbrace => "}".to_string(),
            Token::Semicolon => ";".to_string(),
            Token::Multiplication => "*".to_string(),
            Token::Division => "/".to_string(),
            Token::Plus => "+".to_string(),
            Token::Minus => "-".to_string(),
            Token::Not => "!".to_string(),
            Token::Complement => "~".to_string(),
            Token::Keyword(kw) => match kw {
                Keyword::Int => "int".to_string(),
                Keyword::Return => "return".to_string(),
            },
            Token::Identifier(ident) => ident.to_string(),
            Token::IntLiteral(val) => val.to_string(),
        };
        write!(f, "{}", s)
    }
}

fn token_length(tok: &Token) -> usize {
    match tok {
        Token::Lparen
        | Token::Rparen
        | Token::Lbrace
        | Token::Rbrace
        | Token::Multiplication
        | Token::Division
        | Token::Plus
        | Token::Minus
        | Token::Not
        | Token::Complement
        | Token::Semicolon => 1,
        Token::Keyword(kw) => match kw {
            Keyword::Int => 3,
            Keyword::Return => 6,
        },
        Token::Identifier(ident) => ident.len(),
        Token::IntLiteral(val) => val.to_string().len(),
    }
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
        Token::Plus => r"^\+",
        Token::Minus => r"^-",
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
        Token::Plus,
        Token::Minus,
        Token::Not,
        Token::Complement,
        Token::Keyword(Keyword::Int),
        Token::Keyword(Keyword::Return),
        Token::Identifier("a".to_string()),
        Token::IntLiteral(1),
    ];

    for t in toktypes.iter() {
        let re = Regex::new(get_token_pattern(t)).unwrap();
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
                Token::Lparen
                | Token::Rparen
                | Token::Lbrace
                | Token::Rbrace
                | Token::Semicolon
                | Token::Multiplication
                | Token::Division
                | Token::Plus
                | Token::Minus
                | Token::Not
                | Token::Complement => Ok(t.clone()),
                // _ => Ok(t)
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
        match tok {
            Token::Multiplication | Token::Division => {
                let op = if let Token::Multiplication = tok {
                    BinaryOp::Multiplication
                } else {
                    BinaryOp::Division
                };
                tokiter.next(); // consume
                let next_factor = parse_factor(tokiter);
                factor = Expression::BinaryOp(op, Box::new(factor), Box::new(next_factor));
            }
            _ => {
                break;
            }
        }
    }

    return factor;
}

fn parse_expression(tokiter: &mut Peekable<Iter<Token>>) -> Expression {
    let mut term = parse_term(tokiter);
    while let Some(tok) = tokiter.peek() {
        match tok {
            Token::Minus | Token::Plus => {
                let op = if let Token::Minus = tok {
                    BinaryOp::Subtraction
                } else {
                    BinaryOp::Addition
                };
                tokiter.next(); // consume
                let next_term = parse_term(tokiter);
                term = Expression::BinaryOp(op, Box::new(term), Box::new(next_term));
            }
            _ => {
                break;
            }
        }
    }
    return term;
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

struct Generator {
    emit_32bit: bool,
}

struct Code {
    code: Vec<String>,
}

impl Code {
    fn new() -> Code {
        Code { code: Vec::new() }
    }

    fn pushs(&mut self, mut line: String) {
        line.push('\n');
        self.code.push(line);
    }

    fn push(&mut self, line: &str) {
        self.pushs(line.to_string())
    }

    fn append(&mut self, mut more: Code) {
        self.code.append(&mut more.code);
    }

    fn get_str(self) -> String {
        let mut s = self.code.join("\n");
        s.push('\n');
        return s;
    }
}

impl Generator {
    fn generate_expression_code(&self, expr: &Expression) -> Code {
        let mut code = Code::new();
        match expr {
            Expression::BinaryOp(BinaryOp::Addition, e1, e2) => {
                code = self.generate_expression_code(e1);
                if self.emit_32bit {
                    code.push("    push   %eax");
                } else {
                    code.push("    push   %rax");
                }
                code.append(self.generate_expression_code(e2));
                if self.emit_32bit {
                    code.push("    add    (%esp), %eax"); // add, arg1 is on stack, arg2 is in %eax, and result is in %eax
                    code.push("    add    $4, %esp"); // restore stack pointer
                } else {
                    code.push("    add    (%rsp), %rax"); // add, arg1 is on stack, arg2 is in %eax, and result is in %eax
                    code.push("    add    $8, %rsp"); // restore stack pointer
                }
            }
            Expression::BinaryOp(BinaryOp::Subtraction, e1, e2) => {
                code = self.generate_expression_code(e1);
                if self.emit_32bit {
                    code.push("    push   %eax");
                } else {
                    code.push("    push   %rax");
                }
                code.append(self.generate_expression_code(e2));
                if self.emit_32bit {
                    code.push("    push   %eax"); // push second operand on stack
                    code.push("    mov    4(%esp), %eax"); // restore first operand into %eax
                    code.push("    sub    (%esp), %eax"); // subtract, %eax-(%esp)->%eax
                    code.push("    add    $8, %esp"); // restore stack pointer
                } else {
                    code.push("    push   %rax"); // push second operand on stack
                    code.push("    mov    8(%rsp), %rax"); // restore first operand into %eax
                    code.push("    sub    (%rsp), %rax"); // subtract, %eax-(%esp)->%eax
                    code.push("    add    $16, %rsp"); // restore stack pointer
                }
            }
            Expression::BinaryOp(BinaryOp::Multiplication, e1, e2) => {
                code = self.generate_expression_code(e1);
                if self.emit_32bit {
                    code.push("    push   %eax");
                } else {
                    code.push("    push   %rax");
                }
                code.append(self.generate_expression_code(e2));
                if self.emit_32bit {
                    code.push("    imul   (%esp), %eax"); // multiply, arg1 is on stack, arg2 is in %eax, and result is in %eax
                    code.push("    add    $4, %esp"); // restore stack pointer
                } else {
                    code.push("    imul   (%rsp), %rax"); // multiply, arg1 is on stack, arg2 is in %eax, and result is in %eax
                    code.push("    add    $8, %rsp"); // restore stack pointer
                }
            }
            Expression::BinaryOp(BinaryOp::Division, e1, e2) => {
                code = self.generate_expression_code(e1);
                if self.emit_32bit {
                    code.push("    push   %eax");
                } else {
                    code.push("    push   %rax");
                }
                code.append(self.generate_expression_code(e2));
                if self.emit_32bit {
                    code.push("    push   %eax"); // push second operand on stack
                    code.push("    mov    4(%esp), %eax"); // restore first operand into %eax
                    code.push("    cdq");
                    code.push("    idivl  (%esp)"); // divide, numerator is in %eax, denominator is on stack, and result is in %eax.
                    code.push("    add    $8, %esp"); // restore stack pointer
                } else {
                    code.push("    push   %rax"); // push second operand on stack
                    code.push("    mov    8(%rsp), %rax"); // restore first operand into %eax
                    code.push("    cdq");
                    code.push("    idivl  (%rsp)"); // divide, numerator is in %eax, denominator is on stack, and result is in %eax.
                    code.push("    add    $16, %rsp"); // restore stack pointer
                }
            }
            Expression::UnaryOp(UnaryOp::Negate, expr) => {
                code = self.generate_expression_code(expr);
                if self.emit_32bit {
                    code.push("    neg    %eax");
                } else {
                    code.push("    neg    %rax");
                }
            }
            Expression::UnaryOp(UnaryOp::Not, expr) => {
                code = self.generate_expression_code(expr);
                if self.emit_32bit {
                    code.push("    cmpl   $0, %eax");
                    code.push("    movl   $0, %eax");
                    code.push("    sete   %al");
                } else {
                    code.push("    cmp    $0, %rax");
                    code.push("    mov    $0, %rax");
                    code.push("    sete   %al");
                }
            }
            Expression::UnaryOp(UnaryOp::Complement, expr) => {
                code = self.generate_expression_code(expr);
                if self.emit_32bit {
                    code.push("    not    %eax");
                } else {
                    code.push("    not    %rax");
                }
            }
            Expression::Constant(val) => {
                if self.emit_32bit {
                    code.pushs(format!("    mov    ${}, %eax", val));
                } else {
                    code.pushs(format!("    mov    ${}, %rax", val));
                }
            }
        }
        return code;
    }

    fn generate_statement_code(&self, stmnt: Statement) -> Code {
        let mut code; // = Vec::new();
        match stmnt {
            Statement::Return(expr) => {
                code = self.generate_expression_code(&expr);
                code.push("    ret");
            }
        }
        return code;
    }

    fn generate_program_code(&self, prog: Program) -> Code {
        let mut code = Code::new();
        match prog {
            Program::Program(FunctionDeclaration::Function(name, body)) => {
                code.pushs(format!("    .globl {}", name));
                code.pushs(format!("{}:", name));
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
        .arg(Arg::with_name("32").long("32").help("Generate 32-bit code"))
        .arg(
            Arg::with_name("verbose")
                .short("v")
                .long("verbose")
                .help("Enable verbose output"),
        )
        .get_matches();

    let source_filename = matches.value_of("INPUT").unwrap();
    let source_path = Path::new(source_filename);

    let emit_32bit = matches.is_present("32");
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

    let generator = Generator {
        emit_32bit: emit_32bit,
    };

    let assembly_code = generator.generate_program_code(program);

    fs::write(output_path, assembly_code.get_str()).expect("Failed writing assembly output");
}
