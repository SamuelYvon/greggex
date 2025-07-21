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

#[derive(Debug, Clone)]
pub enum AST {
    Concat(Rc<AST>, Rc<AST>),
    Or(Rc<AST>, Rc<AST>),
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
            AST::Concat(left, right) | AST::Or(left, right) => {
                left.into_postfix(traversal);
                right.into_postfix(traversal);
                traversal.push(Rc::clone(self));
            }
            AST::Repeat(node, _) => {
                node.into_postfix(traversal);
                traversal.push(Rc::clone(self));
            }
            AST::AnyMatch | AST::ExactMatch(_) | AST::InGroup(_) => {
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
    EOS(Cow<'static, str>),
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
            stream.next();
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
        None => Err(ParsingError::EOS("a valid character".into())),
        Some(TokenPos(Token::Character(c), _)) => {
            stream.next();
            Ok(c)
        }
        Some(TokenPos(found, pos)) => Err(UnexpectedToken {
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
        expect_character!(Token::CharGroupRange, stream);
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
                expect_character!(Token::ModStar, stream);
                Some(CountModifier::Star)
            }
            Token::ModAtLeastOnce => {
                expect_character!(Token::ModAtLeastOnce, stream);
                Some(CountModifier::AtLeastOnce)
            }
            Token::ModAtMostOnce => {
                expect_character!(Token::ModAtMostOnce, stream);
                Some(CountModifier::AtMostOnce)
            }
            Token::ModGroupStart => {
                expect_character!(Token::ModGroupStart, stream);

                let start = parse_number(stream)?;

                let range = if let Some(TokenPos(Token::ModComma, _)) = stream.peek() {
                    expect_character!(Token::ModComma, stream);
                    let end = parse_number(stream)?;
                    CountModifier::Range(start..end)
                } else {
                    CountModifier::Exact(start)
                };

                expect_character!(Token::ModGroupEnd, stream);

                Some(range)
            }
            _ => None,
        }),
    }
}

/// Expand a complex repeat modifier into a simpler one. This creates a tree of [AST::Concat].
fn expand_complex_repeat(repeated: Rc<AST>, required: usize, at_most: usize) -> Rc<AST> {
    assert!(at_most >= required);

    let mut sequence = Vec::with_capacity(at_most);

    for _ in 0..required {
        sequence.push(Rc::clone(&repeated));
    }

    for _ in required..at_most {
        sequence.push(Rc::new(AST::Repeat(
            Rc::clone(&repeated),
            CountModifier::AtMostOnce,
        )));
    }

    sequence
        .iter()
        .skip(1)
        .fold(Rc::clone(&sequence[0]), |acc, item| {
            Rc::new(AST::Concat(Rc::clone(&acc), Rc::clone(item)))
        })
}

/// Simplify a counter modifier in a version that does not use a fixed count nor
/// a range. We call these token "complex repeats". The actual expansion is done in
/// [expand_complex_repeat].
fn simplify_modifier(repeated: Rc<AST>, count_modifier: CountModifier) -> Rc<AST> {
    match count_modifier {
        simple @ (CountModifier::Star | CountModifier::AtLeastOnce | CountModifier::AtMostOnce) => {
            Rc::new(AST::Repeat(repeated, simple))
        }
        CountModifier::Exact(n) => expand_complex_repeat(repeated, n, n),
        CountModifier::Range(range) => expand_complex_repeat(repeated, range.start, range.end),
    }
}

fn parse_expr(stream: &mut TokenStream) -> ParsingResult<Rc<AST>> {
    let mut root = Rc::new(AST::Blank);

    let mut or_stack = vec![];

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
                simplify_modifier(node, modifier)
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
                    let group = with_modifier!(parse_char_group(stream)?);
                    push!(group);
                }
                Token::Or => {
                    // This breaks the current group and creates a new one, we parse a new expr.
                    // Push down so the next join does not "grab" the inner group
                    or_stack.push(root);
                    root = Rc::new(AST::Blank);
                }
                // This will get matched recursively, so we abort here
                Token::GroupEnd => {
                    if !or_stack.is_empty() {
                        or_stack.push(root);
                        let ored = or_stack
                            .iter()
                            .skip(1)
                            .fold(Rc::clone(&or_stack[0]), |acc, item| {
                                Rc::new(AST::Or(acc, Rc::clone(item)))
                            });

                        or_stack.clear();

                        root = with_modifier!(ored);
                    } else {
                        root = with_modifier!(root);
                    }

                    break;
                }
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
        AST::Or(l, r) => {
            buff += &postfix(l);
            buff += &postfix(r);
            buff += "|";
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

    fn make_postfix_str(expr: &str) -> String {
        let expr = parse(expr).unwrap();
        postfix(&expr)
    }

    #[test]
    fn test_postfix_simple() {
        assert_eq!(make_postfix_str("a(bb)+a"), "abb.+.a.")
    }

    #[test]
    fn test_simple_letter() {
        assert_eq!(make_postfix_str("a?a?aa"), "a?a?.a.a.");
    }

    #[test]
    fn test_expand_exact_single() {
        assert_eq!(make_postfix_str("a{5}"), "aa.a.a.a.");
    }

    #[test]
    fn test_expand_range_single() {
        assert_eq!(make_postfix_str("a{2,4}"), "aa.a?.a?.");
    }

    #[test]
    fn test_expand_exact_group() {
        assert_eq!(make_postfix_str("(ab){2}"), "ab.ab..");
    }

    #[test]
    fn test_expand_range_group() {
        assert_eq!(make_postfix_str("(ab){2,3}"), "ab.ab..ab.?.")
    }

    #[test]
    fn test_range_edge_case() {
        assert_eq!(make_postfix_str("a{1,2}"), "aa?.")
    }

    #[test]
    fn test_exact_edge_case() {
        assert_eq!(make_postfix_str("a{1}"), "a")
    }

    #[test]
    fn test_char_group_range() {
        assert_eq!(make_postfix_str("[a-d]"), "[a,b,c,d]");
    }

    #[test]
    fn test_char_group() {
        assert_eq!(make_postfix_str("[abcdef]"), "[a,b,c,d,e,f]");
    }

    #[test]
    fn test_choice() {
        assert_eq!(make_postfix_str("(abc|def)"), "ab.c.de.f.|")
    }

    #[test]
    fn test_choices() {
        assert_eq!(make_postfix_str("(a|b|c|d|e)"), "ab|c|d|e|")
    }

    #[test]
    fn test_domain_email_re() {
        println!(
            "{0}",
            make_postfix_str("([a-z]|[A-Z]|[0-9]|[\\._%\\+\\-]){1,2}")
        );
    }
}
