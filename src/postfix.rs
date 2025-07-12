//! Postfix transformation of the parsed regex. The postfix transformation allows us to easily
//! build Thompson NFAs.

use crate::parse::{CountModifier, GregexpToken};

#[derive(Debug)]
pub enum GregexpSegment {
    Character(char),
    Concat,
    Star,
    AtLeastOnce,
    AtMostOnce,
}

fn write_with_mod<F: Fn(&mut Vec<GregexpSegment>)>(
    buffer: &mut Vec<GregexpSegment>,
    writer: F,
    modifier: &Option<CountModifier>,
) {
    writer(buffer);

    match modifier {
        None => (),
        Some(CountModifier::Star) => buffer.push(GregexpSegment::Star),
        Some(CountModifier::AtLeastOnce) => buffer.push(GregexpSegment::AtLeastOnce),
        Some(CountModifier::AtMostOnce) => buffer.push(GregexpSegment::AtMostOnce),
        Some(CountModifier::Exact(repeats)) => {
            for _ in 0..(repeats - 1) {
                writer(buffer);
                buffer.push(GregexpSegment::Concat);
            }
        }
        Some(CountModifier::Range(ranged)) => {
            for _ in 0..(ranged.start - 1) {
                writer(buffer);
                buffer.push(GregexpSegment::Concat);
            }

            let opt = ranged.end - ranged.start;
            for _ in 0..opt {
                writer(buffer);
                buffer.push(GregexpSegment::AtMostOnce);
                buffer.push(GregexpSegment::Concat);
            }
        }
    }
}

fn postfix_sequence(parts: &Vec<GregexpToken>, buffer: &mut Vec<GregexpSegment>) {
    for (i, part) in parts.iter().enumerate() {
        postfix_any(part, buffer);

        // Had something before, has something after.
        if i > 0 {
            buffer.push(GregexpSegment::Concat)
        }
    }
}

fn postfix_exact(value: char, modifier: &Option<CountModifier>, buffer: &mut Vec<GregexpSegment>) {
    write_with_mod(
        buffer,
        |buffer| {
            buffer.push(GregexpSegment::Character(value));
        },
        modifier,
    );
}

fn postfix_group(
    expr: &GregexpToken,
    modifier: &Option<CountModifier>,
    buffer: &mut Vec<GregexpSegment>,
) {
    write_with_mod(
        buffer,
        |buffer| {
            postfix_any(expr, buffer);
        },
        modifier,
    );
}

fn postfix_any(gregexp: &GregexpToken, buffer: &mut Vec<GregexpSegment>) {
    match gregexp {
        GregexpToken::Sequence(parts) => postfix_sequence(parts, buffer),
        GregexpToken::Group(expr, modifier) => postfix_group(expr, modifier, buffer),
        GregexpToken::CharacterGroup(_) => todo!(),
        GregexpToken::ExactMatch(char, modifer) => postfix_exact(*char, modifer, buffer),
    }
}

pub fn postfix(gregexp: &GregexpToken) -> Vec<GregexpSegment> {
    let mut buffer = vec![];
    postfix_any(gregexp, &mut buffer);
    buffer
}

pub fn postfix_to_string(postfix: &Vec<GregexpSegment>) -> String {
    let mut buffer = String::new();

    for segment in postfix {
        match segment {
            GregexpSegment::Character(a) => buffer += &a.to_string(),
            GregexpSegment::Concat => buffer += ".",
            GregexpSegment::AtLeastOnce => buffer += "+",
            GregexpSegment::AtMostOnce => buffer += "?",
            GregexpSegment::Star => buffer += "*",
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
}
