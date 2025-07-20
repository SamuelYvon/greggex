//! Recursive descent parser for a "gregexp". The syntax is the following:
//!
//! <expr> : (<group><modifier>?|<char><modifier>?|<char-group><modifier>?|<any-match><modifier>?)*
//! <any-match> : .
//! <group> : (<expr>(|<expr>)*)
//! <char> : 0-9, a-z, A-Z, !@#$%&*, \<escaped char>
//! <char-group> : [ <range-expr> ]
//! <range-expr> : a-a
//! <escaped-char>: ,^,$,{,},(,),[,],
//! <modifier>: *,+,{l,h}

use crate::lexer::{Token, TokenPos, lex};
use crate::parse::ParsingError::UnexpectedToken;
use std::borrow::Cow;
use std::collections::HashSet;
/// Input stream that is peekable. Used to facilitated parsing and error reporting.
use std::iter::{IntoIterator, Peekable};
use std::ops::Range;
use std::rc::Rc;
use thiserror::Error;

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
    Group(Vec<GregExpToken>, Option<CountModifier>),
    CharacterGroup(HashSet<char>, Option<CountModifier>),
    ExactMatch(char, Option<CountModifier>),
    AnyMatch(Option<CountModifier>),
}

#[derive(Debug, Clone)]
pub enum AST {
    Concat(Rc<AST>, Rc<AST>),
    Repeat(Rc<AST>, CountModifier),
    AnyMatch,
    ExactMatch(char),
    InGroup(HashSet<char>),
    Blank,
}

impl AST {
    pub fn is_blank(&self) -> bool {
        match self {
            AST::Blank => true,
            _ => false,
        }
    }

    pub fn into_postfix(self: &Rc<Self>, traversal: &mut Vec<Rc<AST>>) {
        match self.as_ref() {
            AST::Concat(left, right) => {
                traversal.push(Rc::clone(left));
                traversal.push(Rc::clone(right));
                traversal.push(Rc::clone(self));
            }
            AST::AnyMatch | AST::Repeat(_, _) | AST::ExactMatch(_) | AST::InGroup(_) => {
                traversal.push(Rc::clone(self));
            }
            AST::Blank => (),
        }
    }
}

#[derive(Debug, Error)]
pub enum ParsingError {
    #[error("Unexpected character, expected {expected}, but found {found} at position {pos}.")]
    UnexpectedToken {
        expected: Cow<'static, str>,
        found: Token,
        pos: usize,
    },
    #[error("Unexpected end of input, expected {0}")]
    EOS(char),
    #[error("Unexpected end of input, expected {0}")]
    EOS2(Cow<'static, str>),
}
type ParsingResult<T> = Result<T, ParsingError>;

type TokenStream<'a> = Peekable<std::vec::IntoIter<TokenPos>>;

macro_rules! expect_character {
    ($token_type:pat, $input:expr) => {{
        let ipt: &mut TokenStream = $input;

        match ipt.next() {
            None => panic!("To handle"),
            Some(TokenPos(token, _)) => {
                if !matches!(token, $token_type) {
                    panic!("Not a match");
                }
            }
        }
    }};
}

fn parse_number(stream: &mut TokenStream) -> ParsingResult<usize> {
    let mut result = 0_usize;

    while let Some(TokenPos(Token::Character(c), _)) = stream.peek() {
        if let Some(digit) = c.to_digit(10) {
            result *= 10;
            result += digit as usize;
        } else {
            break;
        }
    }

    Ok(result)
}

/// Parses the next literal character. If the next character is indeed a literal, the stream
/// will be advanced. If not, the stream stays in place. This allows easier conditional parsing.
fn parse_literal(stream: &mut TokenStream) -> ParsingResult<char> {
    let peek = stream.peek().cloned();
    match peek {
        None => Err(ParsingError::EOS2("a valid character".into())),
        Some(TokenPos(Token::Character(c), _)) => {
            stream.next();
            Ok(c)
        }
        Some(TokenPos(found, pos)) => Err(ParsingError::UnexpectedToken {
            expected: "a valid character".into(),
            found,
            pos,
        }),
    }
}

/// Parses a character group.
/// TODO: could be improved by allowing multiple "char-group" at once
fn parse_char_group(stream: &mut TokenStream) -> ParsingResult<Rc<AST>> {
    let mut result = HashSet::new();

    let first_char = parse_literal(stream)?;
    result.insert(first_char);

    if let Some(TokenPos(Token::CharGroupRange, _)) = stream.peek() {
        expect_character!(crate::lexer::Token::CharGroupRange, stream);
        let second_char = parse_literal(stream)?;

        for chr in first_char..=second_char {
            result.insert(chr);
        }
    } else {
        while let Ok(c) = parse_literal(stream) {
            result.insert(c);
        }
    }

    expect_character!(Token::CharGroupEnd, stream);
    Ok(Rc::new(AST::InGroup(result)))
}

fn parse_modifier(stream: &mut TokenStream) -> ParsingResult<Option<CountModifier>> {
    match stream.peek() {
        None => Ok(None),
        Some(TokenPos(token, _)) => Ok(match token {
            Token::ModStar => {
                expect_character!(crate::lexer::Token::ModStar, stream);
                Some(CountModifier::Star)
            }
            Token::ModAtLeastOnce => {
                expect_character!(crate::lexer::Token::ModAtLeastOnce, stream);
                Some(CountModifier::AtLeastOnce)
            }
            Token::ModAtMostOnce => {
                expect_character!(crate::lexer::Token::ModAtMostOnce, stream);
                Some(CountModifier::AtMostOnce)
            }
            Token::ModGroupStart => {
                expect_character!(crate::lexer::Token::ModGroupStart, stream);

                let start = parse_number(stream)?;

                let range = if let Some(TokenPos(Token::ModComma, _)) = stream.peek() {
                    expect_character!(crate::lexer::Token::ModComma, stream);
                    let end = parse_number(stream)?;
                    CountModifier::Range(start..end)
                } else {
                    CountModifier::Exact(start)
                };

                expect_character!(crate::lexer::Token::ModGroupEnd, stream);

                Some(range)
            }
            _ => None,
        }),
    }
}

fn parse_expr(stream: &mut TokenStream) -> ParsingResult<Rc<AST>> {
    let mut root = Rc::new(AST::Blank);

    macro_rules! push {
        ($node:expr) => {{
            let node: Rc<AST> = $node;

            assert!(!node.is_blank(), "We should never push blanks.");

            // Avoid having a CONCAT(BLANK, XYZ)
            // We never push blanksk
            if root.is_blank() {
                root = node;
            } else {
                root = Rc::new(AST::Concat(root, node));
            }
        }};
    }

    macro_rules! with_modifier {
        ($node:expr) => {{
            let node: Rc<AST> = $node;
            if let Some(modifier) = parse_modifier(stream)? {
                Rc::new(AST::Repeat(node, modifier))
            } else {
                node
            }
        }};
    }

    loop {
        match stream.next() {
            None => break,
            Some(TokenPos(token, pos)) => match token {
                Token::Character(chr) => {
                    let node = with_modifier!(Rc::new(AST::ExactMatch(chr)));
                    push!(node);
                }
                Token::CharAny => {
                    push!(with_modifier!(Rc::new(AST::AnyMatch)));
                }
                Token::GroupStart => {
                    let group = with_modifier!(parse_expr(stream)?);
                    push!(group);
                }
                Token::CharGroupStart => {
                    let group = parse_char_group(stream)?;
                    push!(group);
                }
                // This will get matched recursively, so we abort here
                Token::GroupEnd => break,
                // Should **not** be matched in this loop
                found @ (Token::CharGroupRange
                | Token::CharGroupEnd
                | Token::ModStar
                | Token::ModAtLeastOnce
                | Token::ModAtMostOnce
                | Token::ModGroupStart
                | Token::ModGroupEnd
                | Token::ModComma) => {
                    return Err(UnexpectedToken {
                        expected: "a valid start of next group".into(),
                        found,
                        pos,
                    });
                }
            },
        };
    }

    Ok(root)
}

pub fn parse(input: &str) -> ParsingResult<Rc<AST>> {
    let tokens = lex(input);
    let ast = parse_expr(&mut tokens.into_iter().peekable())?;
    Ok(ast)
}

/// Create a postfix representation of the expression. Useful for debugging and testing the
/// parsing.
pub fn postfix<A: AsRef<AST>>(tree: A) -> String {
    let mut buff = String::new();
    
    match tree.as_ref() {
        AST::Concat(l, r) => {
            buff += &postfix(l);
            buff += &postfix(r);
            buff += ".";
        }
        AST::Repeat(node, count) => {
            buff += &postfix(node);
            match count {
                CountModifier::Star => buff += "^*",
                CountModifier::AtLeastOnce => buff += "+",
                CountModifier::AtMostOnce => buff += "?",
                CountModifier::Exact(n) => buff += &format!("^{n}"),
                CountModifier::Range(r) => buff += &format!("^{{{0}-{1}", r.start, r.end),
            }
        }
        AST::AnyMatch => buff += "*",
        AST::ExactMatch(c) => buff += &c.to_string(),
        AST::InGroup(grp) => {
            let mut sorted = grp.iter().map(|c| c.to_string()).collect::<Vec<_>>();
            sorted.sort();

            buff += "[";
            buff += &sorted.join(",");
            buff += "]";
        }
        AST::Blank => (),
    }

    buff
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parsing_simple_repeat() {
        let result = parse("a*").unwrap();
        dbg!(result);
    }

    // #[test]
    // fn test_parsing_modifier() {
    //     let range = "{123,456}";
    //     let result = parse_modifier(&mut stream_of(range)).unwrap();
    //     assert_eq!(result, Some(CountModifier::Range(123..456)));
    // }
    //
    // #[test]
    // fn test_parsing_repeated_a_b() {
    //     let expr = "a{5,6}b";
    //     let result = parse_expr(&mut stream_of(expr)).unwrap();
    //
    //     if let GregExpToken::Sequence(vec) = result {
    //         assert_eq!(2, vec.len());
    //         let a_s = &vec[0];
    //         let b_s = &vec[1];
    //
    //         assert!(matches!(
    //             a_s,
    //             GregExpToken::ExactMatch('a', Some(CountModifier::Range(_)))
    //         ));
    //         assert!(matches!(b_s, GregExpToken::ExactMatch('b', None)));
    //     } else {
    //         panic!("Expected sequence, got: {:?}", result);
    //     }
    // }
    //

    #[test]
    fn test_parsing_simple() {
        let expr = "(he)+llo";
        let result = parse(expr).unwrap();
        assert_eq!(postfix(result), "he.+l.l.o.");
    }

    #[test]
    fn test_parsing_char_group() {
        let expr = "[a-z]";
        let result = parse(expr).unwrap();
        dbg!(result);
    }
}
