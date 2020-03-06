extern crate regex;
use regex::Regex;
use std::error;
use std::fmt;

//===================================================================
// Tokenizing
//===================================================================

#[derive(Debug, Copy, Clone)]
pub enum Keyword {
    Int,
    Return,
}

#[derive(Debug, Clone)]
pub enum Token {
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

fn keyword_to_str(kw: Keyword) -> String {
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
        Token::Keyword(kw) => keyword_to_str(*kw),
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
        Token::Keyword(kw) => format!(r"^{}\W", keyword_to_str(*kw)),
        Token::Identifier(_) => r"^([a-zA-Z]\w*)".to_string(),
        Token::IntLiteral(_) => r"^([0-9]+)".to_string(),
        _ => format!("^{}", regex::escape(&token_to_str(tok))),
    }
}

#[derive(Debug, Clone)]
pub struct TokenError {
    pub cursor: usize,
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
        let re = Regex::new(&get_token_pattern(t))
            .unwrap_or_else(|_| panic!("Failed building regex object for token type {:?}", t));
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
    Err(TokenError { cursor })
}

pub struct TokNLoc {
    pub token: Token,
    pub location: usize,
    pub length: usize,
}

impl TokNLoc {
    fn new(tok: Token, loc: usize, len: usize) -> TokNLoc {
        TokNLoc { token: tok, location: loc, length: len }
    }
}

pub fn tokenize(source: &str) -> Result<Vec<TokNLoc>, TokenError> {
    let mut result = Vec::new();

    let len = source.len();
    let mut cursor = 0;

    let re_space = Regex::new(r"^\p{White_Space}").unwrap();

    while cursor < len {
        if re_space.is_match(&source[cursor..]) {
            cursor += 1;
            continue;
        }

        let tok = get_token(source, cursor)?;
        let toklen = token_length(&tok);
        result.push(TokNLoc::new(tok, cursor, toklen));
        cursor += toklen;
    }

    Ok(result)
}
