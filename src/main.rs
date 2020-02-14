extern crate regex;
extern crate clap;
use regex::Regex;
use clap::{App,Arg};
use std::fs;
use std::error;
use std::fmt;
use std::path::{Path,PathBuf};
use core::slice::Iter;

#[derive(Debug,Copy,Clone)]
enum Keyword {
    Int,
    Return
}

#[derive(Debug)]
enum Token {
    Semicolon,
    Lparen,
    Rparen,
    Lbrace,
    Rbrace,
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
            Token::Minus => "-".to_string(),
            Token::Not => "!".to_string(),
            Token::Complement => "~".to_string(),
            Token::Keyword(kw) => match kw {
                Keyword::Int => "int".to_string(),
                Keyword::Return => "return".to_string()
            }
            Token::Identifier(ident) => ident.to_string(),
            Token::IntLiteral(val) => val.to_string()
        };
        write!(f, "{}", s)
    }
}

fn token_length(tok: &Token) -> usize {
    match tok {
        Token::Lparen|Token::Rparen|
        Token::Lbrace|Token::Rbrace|
        Token::Minus|Token::Not|Token::Complement|
        Token::Semicolon
            => 1,
        Token::Keyword(kw) => match kw {
            Keyword::Int => 3,
            Keyword::Return => 6
        }
        Token::Identifier(ident) => ident.len(),
        Token::IntLiteral(val) => val.to_string().len()
    }
}

fn get_token_pattern(tok: &Token) -> &str {
    match tok {
        Token::Lparen => r"^\(",
        Token::Rparen => r"^\)",
        Token::Lbrace => r"^\{",
        Token::Rbrace => r"^\}",
        Token::Semicolon => r"^;",
        Token::Minus => r"^-",
        Token::Not => r"^!",
        Token::Complement => r"^~",
        Token::Keyword(kw) => match kw {
            Keyword::Int => r"^int\W",
            Keyword::Return => r"^return\W"
        }
        Token::Identifier(_) => r"([a-zA-Z]\w*)",
        Token::IntLiteral(_) => r"([0-9]+)"
    }
}

#[derive(Debug,Clone)]
struct TokenError
{
    cursor: usize
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

fn get_token(source: &str, cursor: usize) -> Result<Token,TokenError>
{
    let toktypes = [Token::Semicolon,
                    Token::Lparen, Token::Rparen,
                    Token::Lbrace, Token::Rbrace,
                    Token::Lbrace, Token::Rbrace,
                    Token::Minus,Token::Not,Token::Complement,
                    Token::Keyword(Keyword::Int),
                    Token::Keyword(Keyword::Return),
                    Token::Identifier("a".to_string()),
                    Token::IntLiteral(1)];

    for t in toktypes.iter() {

        let re = Regex::new(get_token_pattern(t)).unwrap();
        if let Some(caps) = re.captures(&source[cursor..])
        {
            return
                match t {
                    Token::Identifier(_) => {
                        let ident_cap = caps.get(1).expect("asdfb");
                        let ident = ident_cap.as_str().to_string();
                        Ok(Token::Identifier(ident))
                    }

                    Token::IntLiteral(_) => {
                        let value: i64 = caps.get(1)
                            .unwrap()
                            .as_str()
                            .parse()
                            .unwrap();
                        Ok(Token::IntLiteral(value))
                    }
                    Token::Lparen => Ok(Token::Lparen),
                    Token::Rparen => Ok(Token::Rparen),
                    Token::Lbrace => Ok(Token::Lbrace),
                    Token::Rbrace => Ok(Token::Rbrace),
                    Token::Semicolon => Ok(Token::Semicolon),
                    Token::Minus => Ok(Token::Minus),
                    Token::Not => Ok(Token::Not),
                    Token::Complement => Ok(Token::Complement),
                    Token::Keyword(kw) => Ok(Token::Keyword(*kw))
                }
        }
    }
    return Err(TokenError {cursor: cursor})
}


fn tokenize(source: &str) -> Vec<Token>
{
    let mut result = Vec::new();

    let len = source.len();
    let mut cursor = 0;

    let re_space = Regex::new(r"^\p{White_Space}").unwrap();

    while cursor < len  {

        if re_space.is_match(&source[cursor..]) {
            cursor += 1;
            continue;
        }

        let tok = get_token(source,cursor).unwrap();
        cursor += token_length(&tok);
        result.push(tok);
    }

    return result
}

#[derive(Debug)]
enum UnaryOp {
    Negate,
    Not,
    Complement
}

#[derive(Debug)]
enum Expression {
    UnaryOp(UnaryOp,Box<Expression>),
    Constant(i64)
}

#[derive(Debug)]
enum Statement {
    Return(Expression)
}

#[derive(Debug)]
enum FunctionDeclaration {
    Function(String,Statement)
}

#[derive(Debug)]
enum Program {
    Program(FunctionDeclaration)
}

fn parse_expression(tokiter: &mut Iter<Token>) -> Expression {
    // ensure first and only token is an int literal.
    let tok = tokiter.next().unwrap();
    match tok {
        Token::IntLiteral(v) => Expression::Constant(*v),
        Token::Minus => Expression::UnaryOp(UnaryOp::Negate,Box::new(parse_expression(tokiter))),
        Token::Not => Expression::UnaryOp(UnaryOp::Not,Box::new(parse_expression(tokiter))),
        Token::Complement => Expression::UnaryOp(UnaryOp::Complement,Box::new(parse_expression(tokiter))),
        _ => panic!("Invalid expression. Expected an integer literal, got '{}'.",tok)
    }
}

fn parse_statement(tokiter: &mut Iter<Token>) -> Statement {
    // ensure first token is a Return keyword
    let mut tok = tokiter.next().unwrap();
    match tok {
        Token::Keyword(Keyword::Return) => (),
        _ => panic!("Invalid statement. Expected 'return' keyword, got '{}'.",tok)
    }

    let expression = parse_expression(tokiter);

    // ensure last token is a semicolon
    tok = tokiter.next().unwrap();
    match tok {
        Token::Semicolon => (),
        _ => panic!("Invalid statement. Expected a final semicolon, got '{}'.",tok)
    }

    return Statement::Return(expression);
}

fn parse_function(tokiter: &mut Iter<Token>) -> FunctionDeclaration {

    // ensure first token is an Int keyword
    let mut tok = tokiter.next().unwrap();
    match tok {
        Token::Keyword(Keyword::Int) => (),
        _ => panic!("Invalid function declaration. Expected return type, got '{}'.",tok)
    }

    // next token should be an identifier
    tok = tokiter.next().unwrap();
    let function_name = match tok {
        Token::Identifier(ident) => ident,
        _ => panic!("Invalid function declaration. Expected identifier, got '{}'.",tok)
    };

    // ensure next token is '('
    tok = tokiter.next().unwrap();
    match tok {
        Token::Lparen => (),
        _ => panic!("Invalid function declaration. Expected '(', got '{}'.",tok)
    }

    // ensure next token is ')'
    tok = tokiter.next().unwrap();
    match tok {
        Token::Rparen => (),
        _ => panic!("Invalid function declaration. Expected ')', got '{}'.",tok)
    }

    // ensure next token is '{'
    tok = tokiter.next().unwrap();
    match tok {
        Token::Lbrace => (),
        _ => panic!("Invalid function declaration. Expected '{{', got '{}'.",tok)
    }

    // parse statement
    let statement = parse_statement(tokiter);

    // ensure next token is '}'
    tok = tokiter.next().unwrap();
    match tok {
        Token::Rbrace => (),
        _ => panic!("Invalid function declaration. Expected '}}', got '{}'.",tok)
    }

    return FunctionDeclaration::Function(function_name.to_string(),statement)
}

fn parse_program(tokiter: &mut Iter<Token>) -> Program {
    return Program::Program(parse_function(tokiter));
}

fn parse(tokens: &[Token]) -> Program
{
    let mut tokiter = tokens.iter();
    return parse_program(&mut tokiter);
}

struct Code {
    code: Vec<String>
}

impl Code {
    fn new() -> Code{
        Code { code:Vec::new() }
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
        return s
    }
}

fn generate_expression_code(expr: &Expression) -> Code {
    let mut code = Code::new();
    match expr {
        Expression::UnaryOp(UnaryOp::Negate,expr) => {
            code = generate_expression_code(expr);
            code.push("    neg    %eax");
        }
        Expression::UnaryOp(UnaryOp::Not,expr) => {
            code = generate_expression_code(expr);
            code.push("    cmpl   $0, %eax");
            code.push("    movl   $0, %eax");
            code.push("    sete   %al");
        }
        Expression::UnaryOp(UnaryOp::Complement,expr) => {
            code = generate_expression_code(expr);
            code.push("    not    %eax");
        }
        Expression::Constant(val) => {
            code.pushs(format!("    mov    ${}, %eax",val));
        }
    }
    return code;
}

fn generate_statement_code(stmnt: Statement) -> Code {
    let mut code;// = Vec::new();
    match stmnt {
        Statement::Return(expr) => {
            code = generate_expression_code(&expr);
            code.push("    ret");
        }
    }
    return code;
}

fn generate_program_code(prog: Program) -> Code {
    let mut code = Code::new();
    match prog {
        Program::Program(FunctionDeclaration::Function(name,body)) => {
            code.pushs(format!("    .globl {}",name));
            code.pushs(format!("{}:",name));
            code.append(generate_statement_code(body));
        }
    }
    return code;
}

fn main() {
    let matches = App::new("c-compiler")
        .arg(Arg::with_name("INPUT")
             .help("The source file to compile")
             .required(true))
        .arg(Arg::with_name("output")
             .short("o")
             .long("output")
             .value_name("OUTPUT")
             .help("The output assembly file (INPUT with suffix .s by default)"))
        .get_matches();

    let source_filename = matches.value_of("INPUT").unwrap();
    let source_path     = Path::new(source_filename);

    match source_path.extension() {
        Some(x) if x.to_str() == Some("c") => (),
        _ => {
            println!("Expected c source file with extension .c");
            std::process::exit(1)
        }
    }

    let output_path: PathBuf = match matches.value_of("OUTPUT") {
        Some(p) => PathBuf::from(p),
        None => {
            source_path.with_extension("s")
        }
    };

    // println!("Compiling {} -> {}...",source_path.display(),output_path.display());

    let source = fs::read_to_string(source_path)
        .expect("Failed reading source file");

    // println!("Got source:");
    // println!("{}",source);

    let tokens = tokenize(&source);

    // println!("After tokenization:");
    // let tokenstrs: Vec<String> = tokens.iter().map(|t| {
    //     format!("{}",t)
    // }).collect();
    // println!("{}",tokenstrs.join(" "));

    let program = parse(&tokens);

    // println!("After parsing:");
    // println!("{:?}",program);

    let assembly_code = generate_program_code(program);

    fs::write(output_path, assembly_code.get_str()).expect("Failed writing assembly output");
}
