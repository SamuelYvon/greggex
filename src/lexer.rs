use core::panic;
use std::fmt::Display;
use std::{
    iter::{Enumerate, Peekable},
    str::Chars,
};

pub type Pos = usize;

#[derive(Debug, Clone)]
pub enum Token {
    Character(char),
    CharAny,
    GroupStart,
    GroupEnd,
    ModStar,
    ModAtLeastOnce,
    ModAtMostOnce,
    ModGroupStart,
    ModGroupEnd,
    ModComma,
    CharGroupStart,
    CharGroupEnd,
    CharGroupRange,
    Or,
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // TODO
        std::fmt::Debug::fmt(self, f)
    }
}

#[derive(Debug, Clone)]
pub struct TokenPos(pub Token, pub Pos);

type CharStream<'a> = Peekable<Enumerate<Chars<'a>>>;

fn stream_of(input: &str) -> CharStream {
    let chars = input.chars().enumerate();
    chars.peekable()
}

pub fn lex(input: &str) -> Vec<TokenPos> {
    let mut lexed = Vec::with_capacity(input.len()); // Probably close enough
    let mut stream = stream_of(input);

    while let Some((i, chr)) = stream.next() {
        let pos = i as Pos;

        let token = match chr {
            chr if chr >= 'a' && chr <= 'z' => Token::Character(chr),
            chr if chr >= 'A' && chr <= 'Z' => Token::Character(chr),
            chr if chr >= '0' && chr <= '9' => Token::Character(chr),
            chr @ '@' => Token::Character(chr),
            chr @ '!' => Token::Character(chr),
            chr @ '#' => Token::Character(chr),
            chr @ '%' => Token::Character(chr),
            chr @ '=' => Token::Character(chr),
            chr @ '"' => Token::Character(chr),
            chr @ '\'' => Token::Character(chr),
            chr @ '&' => Token::Character(chr),
            chr @ '_' => Token::Character(chr),
            chr @ ':' => Token::Character(chr),
            chr @ ';' => Token::Character(chr),
            '+' => Token::ModAtLeastOnce,
            '?' => Token::ModAtMostOnce,
            '*' => Token::ModStar,
            '(' => Token::GroupStart,
            ')' => Token::GroupEnd,
            '[' => Token::CharGroupStart,
            ']' => Token::CharGroupEnd,
            '{' => Token::ModGroupStart,
            '}' => Token::ModGroupEnd,
            ',' => Token::ModComma,
            '-' => Token::CharGroupRange,
            '.' => Token::CharAny,
            '|' => Token::Or,
            '\\' => match stream.next() {
                None => todo!(),
                Some((_, chr @ '+')) => Token::Character(chr),
                Some((_, chr @ '?')) => Token::Character(chr),
                Some((_, chr @ '*')) => Token::Character(chr),
                Some((_, chr @ '(')) => Token::Character(chr),
                Some((_, chr @ ')')) => Token::Character(chr),
                Some((_, chr @ '[')) => Token::Character(chr),
                Some((_, chr @ ']')) => Token::Character(chr),
                Some((_, chr @ '{')) => Token::Character(chr),
                Some((_, chr @ '}')) => Token::Character(chr),
                Some((_, chr @ ',')) => Token::Character(chr),
                Some((_, chr @ '-')) => Token::Character(chr),
                Some((_, chr @ '.')) => Token::Character(chr),
                Some((_, chr @ '|')) => Token::Character(chr),
                Some((_, chr)) => panic!("Unhandled character: {chr}"),
            },
            chr => panic!("Unhandled character: {chr}"),
        };

        lexed.push(TokenPos(token, pos));
    }

    lexed
}
