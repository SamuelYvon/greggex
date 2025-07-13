//! Postfix transformation of the parsed regex. The postfix transformation allows us to easily
//! build Thompson NFAs.

use crate::parse::{CountModifier, GregExpToken};
use std::collections::HashSet;

#[derive(Debug)]
pub enum GregExpSegment {
    AnyMatch,
    Character(char),
    Set(HashSet<char>),
    Or,
    Concat,
    Star,
    AtLeastOnce,
    AtMostOnce,
}

fn write_with_mod<F: Fn(&mut Vec<GregExpSegment>)>(
    buffer: &mut Vec<GregExpSegment>,
    writer: F,
    modifier: &Option<CountModifier>,
) {
    writer(buffer);

    match modifier {
        None => (),
        Some(CountModifier::Star) => buffer.push(GregExpSegment::Star),
        Some(CountModifier::AtLeastOnce) => buffer.push(GregExpSegment::AtLeastOnce),
        Some(CountModifier::AtMostOnce) => buffer.push(GregExpSegment::AtMostOnce),
        Some(CountModifier::Exact(repeats)) => {
            for _ in 0..(repeats - 1) {
                writer(buffer);
                buffer.push(GregExpSegment::Concat);
            }
        }
        Some(CountModifier::Range(ranged)) => {
            for _ in 0..(ranged.start - 1) {
                writer(buffer);
                buffer.push(GregExpSegment::Concat);
            }

            let opt = ranged.end - ranged.start;
            for _ in 0..opt {
                writer(buffer);
                buffer.push(GregExpSegment::AtMostOnce);
                buffer.push(GregExpSegment::Concat);
            }
        }
    }
}

fn postfix_sequence(parts: &Vec<GregExpToken>, buffer: &mut Vec<GregExpSegment>) {
    for (i, part) in parts.iter().enumerate() {
        postfix_any(part, buffer);

        // Had something before, has something after.
        if i > 0 {
            buffer.push(GregExpSegment::Concat)
        }
    }
}

fn postfix_exact(value: char, modifier: &Option<CountModifier>, buffer: &mut Vec<GregExpSegment>) {
    write_with_mod(
        buffer,
        |buffer| {
            buffer.push(GregExpSegment::Character(value));
        },
        modifier,
    );
}

fn postfix_group(
    exprs: &Vec<GregExpToken>,
    modifier: &Option<CountModifier>,
    buffer: &mut Vec<GregExpSegment>,
) {
    write_with_mod(
        buffer,
        |buffer| {
            for (i, expr) in exprs.iter().enumerate() {
                postfix_any(expr, buffer);

                if i > 0 {
                    buffer.push(GregExpSegment::Or);
                }
            }
        },
        modifier,
    );
}

fn postfix_character_group(
    charset: &HashSet<char>,
    modifier: &Option<CountModifier>,
    buffer: &mut Vec<GregExpSegment>,
) {
    write_with_mod(
        buffer,
        |buffer| {
            buffer.push(GregExpSegment::Set(charset.clone()));
        },
        modifier,
    );
}

fn postfix_any_match(modifier: &Option<CountModifier>, buffer: &mut Vec<GregExpSegment>) {
    write_with_mod(
        buffer,
        |buffer| buffer.push(GregExpSegment::AnyMatch),
        modifier,
    )
}

fn postfix_any(gregexp: &GregExpToken, buffer: &mut Vec<GregExpSegment>) {
    match gregexp {
        GregExpToken::AnyMatch(modifier) => postfix_any_match(modifier, buffer),
        GregExpToken::Sequence(parts) => postfix_sequence(parts, buffer),
        GregExpToken::Group(exprs, modifier) => postfix_group(exprs, modifier, buffer),
        GregExpToken::CharacterGroup(charset, modifier) => {
            postfix_character_group(charset, modifier, buffer)
        }
        GregExpToken::ExactMatch(char, modifier) => postfix_exact(*char, modifier, buffer),
    }
}

pub fn postfix(gregexp: &GregExpToken) -> Vec<GregExpSegment> {
    let mut buffer = vec![];
    postfix_any(gregexp, &mut buffer);
    buffer
}

#[allow(unused)]
pub fn postfix_to_string(postfix: &Vec<GregExpSegment>) -> String {
    let mut buffer = String::new();
    let mut charsets = vec![];

    for segment in postfix {
        match segment {
            GregExpSegment::Character(a) => buffer += &a.to_string(),
            GregExpSegment::Concat => buffer += ".",
            GregExpSegment::Or => buffer += "|",
            GregExpSegment::AtLeastOnce => buffer += "+",
            GregExpSegment::AtMostOnce => buffer += "?",
            GregExpSegment::Star => buffer += "*",
            GregExpSegment::Set(charset) => {
                let mut values = charset.iter().map(|c| c.to_string()).collect::<Vec<_>>();
                values.sort();

                buffer += &format!("<s{0}>", charsets.len() + 1);
                charsets.push(values.join(","));
            }
            GregExpSegment::AnyMatch => {
                buffer += "<any>";
            }
        }
    }

    if charsets.len() > 0 {
        buffer += "\n";
        for (i, charset) in charsets.iter().enumerate() {
            buffer += &format!("s{0} = {charset}\n", i + 1);
        }
    }

    buffer
}

#[cfg(test)]
mod tests {
    use crate::parse::parse;
    use crate::postfix::{postfix, postfix_to_string};

    fn make_postfix_str(expr: &str) -> String {
        let expr = parse(expr).unwrap();
        let postfix = postfix(&expr);
        postfix_to_string(&postfix)
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
        assert_eq!(make_postfix_str("[a-d]"), "<s1>\ns1 = a,b,c,d\n");
    }

    #[test]
    fn test_char_group() {
        assert_eq!(make_postfix_str("[abcdef]"), "<s1>\ns1 = a,b,c,d,e,f\n");
    }

    #[test]
    fn test_choice() {
        assert_eq!(make_postfix_str("(abc|def)"), "ab.c.de.f.|")
    }

    #[test]
    fn test_choices() {
        assert_eq!(make_postfix_str("(a|b|c|d|e)"), "ab|c|d|e|")
    }
}
