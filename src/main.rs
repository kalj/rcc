extern crate regex;
extern crate clap;
use regex::Regex;
use clap::{App,Arg};
use std::fs;
use std::error;
use std::fmt;
use std::path::{Path,PathBuf};

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
        Token::Lparen => 1,
        Token::Rparen => 1,
        Token::Lbrace => 1,
        Token::Rbrace => 1,
        Token::Semicolon => 1,
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

    let program =
"	.globl	main
main:
	movl	$2, %eax
	ret
";

    fs::write(output_path, program).expect("Failed writing assembly output");
}
