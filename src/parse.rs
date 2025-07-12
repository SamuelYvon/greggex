//! Recursive descent parser for a "gregexp". The syntax is the following:
//!
//! <expr> : (<group><modifier>?|<char><modifier>?|<char-group><modifier>?)*
//! <group> : (<expr>)
//! <char> : 0-9, a-z, A-Z, !@#$%&*, \<escaped char>
//! <char-group> : [ <range-expr> ]
//! <range-expr> : a-a
//! <escaped-char>: ,,^,$,{,},(,),[,],
//! <modifier>: *,+,{l,h}

use crate::parse::GregExpToken::{CharacterGroup, Sequence};
use std::borrow::Cow;
use std::collections::HashSet;
/// Input stream that is peekable. Used to facilitated parsing and error reporting.
use std::iter::{Enumerate, Peekable};
use std::ops::Range;
use std::rc::Rc;
use std::str::Chars;
use thiserror::Error;

const GROUP_START: char = '(';
const GROUP_END: char = ')';
const CHAR_GROUP_START: char = '[';
const CHAR_GROUP_END: char = ']';
const CHAR_MODIFIER_STAR: char = '*';
const CHAR_MODIFIER_AT_LEAST_ONE: char = '+';
const CHAR_MODIFIER_RANGE_START: char = '{';
const CHAR_MODIFIER_RANGE_END: char = '}';
const CHAR_MODIFIER_AT_MOST_ONCE: char = '?';

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CountModifier {
    Star,
    AtLeastOnce,
    AtMostOnce,
    Exact(usize),
    Range(Range<usize>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GregExpToken {
    Sequence(Vec<GregExpToken>),
    Group(Rc<GregExpToken>, Option<CountModifier>),
    CharacterGroup(HashSet<char>, Option<CountModifier>),
    ExactMatch(char, Option<CountModifier>),
}

#[derive(Debug, PartialEq, Eq, Clone, Error)]
pub enum ParsingError {
    #[error("Unexpected character, expected {expected}, found {found} at position {pos}.")]
    UnexpectedCharacter {
        expected: char,
        found: char,
        pos: usize,
    },
    #[error(
        "Unexpected character, expected a valid {description}, but found {found} at position {pos}."
    )]
    UnexpectedCharacter2 {
        description: Cow<'static, str>,
        found: char,
        pos: usize,
    },
    #[error("Unexpected end of input, expected {0}")]
    EOS(char),
    #[error("Unexpected end of input, expected {0}")]
    EOS2(Cow<'static, str>),
}

type TokenStream<'a> = Peekable<Enumerate<Chars<'a>>>;

pub type ParsingResult<T> = Result<T, ParsingError>;

macro_rules! expect_char {
    ($char:expr, $stream:expr) => {{
        let expected: char = $char;
        let s: &mut TokenStream = $stream;
        match s.next() {
            None => return Err(ParsingError::EOS(expected)),
            Some((pos, found)) if found != expected => {
                return Err(ParsingError::UnexpectedCharacter {
                    expected,
                    found,
                    pos,
                });
            }
            Some(_) => (),
        };
    }};
}

/// Parses a non-negative number from the input stream.
fn parse_number(input: &mut TokenStream) -> ParsingResult<usize> {
    let mut number = 0_usize;

    if input.peek().is_none() {
        return Err(ParsingError::EOS2("a digit".into()));
    }

    // At least one by above check
    while let Some((_, digit)) = input.next_if(|(_, c)| c.is_digit(10)) {
        number *= 10;
        number += digit.to_digit(10).expect("Checked by the above condition") as usize;
    }

    Ok(number)
}

/// Checks if the next character is valid for a single character input
fn next_character_is_valid(input: &mut TokenStream) -> bool {
    match input.peek() {
        None => false,
        Some((_, c)) if *c >= 'a' && *c <= 'z' => true,
        Some((_, c)) if *c >= 'A' && *c <= 'Z' => true,
        Some((_, c)) if *c >= '0' && *c <= '9' => true,
        Some((_, '@')) => true,
        Some((_, '!')) => true,
        Some((_, '#')) => true,
        Some((_, '%')) => true,
        Some((_, '=')) => true,
        Some((_, '"')) => true,
        Some((_, '\'')) => true,
        Some((_, '&')) => true,
        Some((_, '-')) => true,
        Some((_, ',')) => true,
        Some((_, ':')) => true,
        Some((_, ';')) => true,
        Some((_, '\\')) => true,
        Some((_, _)) => false,
    }
}

/// Parses a single character a literal regex input. Will read escaped character
fn parse_single_character(input: &mut TokenStream) -> ParsingResult<char> {
    match input.next() {
        None => Err(ParsingError::EOS2("a character".into())),
        Some((_, c)) if c >= 'a' && c <= 'z' => Ok(c),
        Some((_, c)) if c >= 'A' && c <= 'Z' => Ok(c),
        Some((_, c)) if c >= '0' && c <= '9' => Ok(c),
        Some((_, c @ '@')) => Ok(c),
        Some((_, c @ '!')) => Ok(c),
        Some((_, c @ '#')) => Ok(c),
        Some((_, c @ '%')) => Ok(c),
        Some((_, c @ '=')) => Ok(c),
        Some((_, c @ '"')) => Ok(c),
        Some((_, c @ '\'')) => Ok(c),
        Some((_, c @ '&')) => Ok(c),
        Some((_, c @ '-')) => Ok(c),
        Some((_, c @ ',')) => Ok(c),
        Some((_, c @ ':')) => Ok(c),
        Some((_, c @ ';')) => Ok(c),
        Some((_, '\\')) => match input.next() {
            None => Err(ParsingError::EOS2("any escapable character".into())),
            Some((_, c @ '(')) => Ok(c),
            Some((_, c @ ')')) => Ok(c),
            Some((_, c @ '[')) => Ok(c),
            Some((_, c @ ']')) => Ok(c),
            Some((_, c @ '{')) => Ok(c),
            Some((_, c @ '}')) => Ok(c),
            Some((_, c @ '$')) => Ok(c),
            Some((_, c @ '^')) => Ok(c),
            Some((pos, found)) => Err(ParsingError::UnexpectedCharacter2 {
                description: "any escapable character".into(),
                found,
                pos,
            }),
        },
        Some((pos, found)) => Err(ParsingError::UnexpectedCharacter2 {
            description: "a valid character".into(),
            found,
            pos,
        }),
    }
}

/// Parses a count modifier for a token.
fn parse_modifier(input: &mut TokenStream) -> ParsingResult<Option<CountModifier>> {
    // At least one character
    let next = input.peek();

    match next {
        Some((_, CHAR_MODIFIER_STAR)) => {
            expect_char!(CHAR_MODIFIER_STAR, input);
            Ok(Some(CountModifier::Star))
        }
        Some((_, CHAR_MODIFIER_AT_LEAST_ONE)) => {
            expect_char!(CHAR_MODIFIER_AT_LEAST_ONE, input);
            Ok(Some(CountModifier::AtLeastOnce))
        }
        Some((_, CHAR_MODIFIER_AT_MOST_ONCE)) => {
            expect_char!(CHAR_MODIFIER_AT_MOST_ONCE, input);
            Ok(Some(CountModifier::AtMostOnce))
        }
        Some((_, CHAR_MODIFIER_RANGE_START)) => {
            expect_char!(CHAR_MODIFIER_RANGE_START, input);
            let n1 = parse_number(input)?;

            let modifier = if matches!(input.peek(), Some((_, ','))) {
                expect_char!(',', input);
                let n2 = parse_number(input)?;
                CountModifier::Range(n1..n2)
            } else {
                CountModifier::Exact(n1)
            };

            expect_char!(CHAR_MODIFIER_RANGE_END, input);

            Ok(Some(modifier))
        }
        _ => Ok(None),
    }
}

fn parse_char_group(input: &mut TokenStream) -> ParsingResult<HashSet<char>> {
    let first = parse_single_character(input)?;

    let mut values = HashSet::new();

    match input.peek() {
        None => (),
        // It's a 'dynamic' ascii range.
        Some((_, '-')) => {
            expect_char!('-', input);
            let second = parse_single_character(input)?;
            for c in first..=second {
                values.insert(c);
            }
        }
        // It's a sequence of characters that are or-d
        Some((_, _)) => {
            values.insert(first);
            while next_character_is_valid(input) {
                values.insert(parse_single_character(input)?);
            }
        }
    }

    Ok(values)
}

/// Parse an expression.
fn parse_expr(input: &mut TokenStream) -> ParsingResult<GregExpToken> {
    let mut ret = vec![];

    while let Some(peeked) = input.peek() {
        match peeked {
            (_, GROUP_START) => {
                expect_char!(GROUP_START, input);
                let expr = parse_expr(input)?;
                expect_char!(GROUP_END, input);
                let modifier = parse_modifier(input)?;
                ret.push(GregExpToken::Group(Rc::new(expr), modifier));
            }
            (_, GROUP_END) => break,
            (_, CHAR_GROUP_START) => {
                expect_char!(CHAR_GROUP_START, input);
                let values = parse_char_group(input)?;
                expect_char!(CHAR_GROUP_END, input);
                let modifier = parse_modifier(input)?;
                ret.push(CharacterGroup(values, modifier));
            }
            (_, CHAR_GROUP_END) => break,
            (_, _) => {
                let char = parse_single_character(input)?;
                let modifier = parse_modifier(input)?;
                ret.push(GregExpToken::ExactMatch(char, modifier))
            }
        }
    }

    Ok(Sequence(ret))
}

fn stream_of(input: &str) -> TokenStream {
    let chars = input.chars().enumerate();
    chars.peekable()
}

pub fn parse(gregexp: &str) -> ParsingResult<GregExpToken> {
    let token_stream = stream_of(gregexp);
    parse_expr(&mut token_stream.into())
}

#[cfg(test)]
mod tests {
    use crate::parse::{CountModifier, GregExpToken, parse_expr, parse_modifier, stream_of};

    #[test]
    fn test_parsing_modifier() {
        let range = "{123,456}";
        let result = parse_modifier(&mut stream_of(range)).unwrap();
        assert_eq!(result, Some(CountModifier::Range(123..456)));
    }

    #[test]
    fn test_parsing_repeated_a_b() {
        let expr = "a{5,6}b";
        let result = parse_expr(&mut stream_of(expr)).unwrap();

        if let GregExpToken::Sequence(vec) = result {
            assert_eq!(2, vec.len());
            let a_s = &vec[0];
            let b_s = &vec[1];

            assert!(matches!(
                a_s,
                GregExpToken::ExactMatch('a', Some(CountModifier::Range(_)))
            ));
            assert!(matches!(b_s, GregExpToken::ExactMatch('b', None)));
        } else {
            panic!("Expected sequence, got: {:?}", result);
        }
    }

    #[test]
    fn test_parsing_char_group() {
        let expr = "[a-z]";
        let result = parse_expr(&mut stream_of(expr)).unwrap();

        if let GregExpToken::Sequence(vec) = result {
            assert!(matches!(vec[0], GregExpToken::CharacterGroup(_, None)));
        } else {
            panic!("Expected Vec<CharGroup>, got: {:?}", result);
        }
    }
}
