//! Postfix transformation of the parsed regex. The postfix transformation allows us to easily
//! build Thompson NFAs.

use crate::parse::{CountModifier, GregexpToken};

#[derive(Debug)]
pub enum GregexpSegment {
    Character(char),
    Concat,
    CountModifier(CountModifier),
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
    // TODO: simplification of exact and range?
    buffer.push(GregexpSegment::Character(value));
    if let Some(modifier) = modifier.clone() {
        buffer.push(GregexpSegment::CountModifier(modifier))
    }
}

fn postfix_group(
    expr: &GregexpToken,
    modifier: &Option<CountModifier>,
    buffer: &mut Vec<GregexpSegment>,
) {
    postfix_any(expr, buffer);
    if let Some(modifier) = modifier.clone() {
        buffer.push(GregexpSegment::CountModifier(modifier));
    }
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
            GregexpSegment::CountModifier(modifier) => match modifier {
                CountModifier::Star => buffer += "*",
                CountModifier::AtLeastOnce => buffer += "+",
                CountModifier::AtMostOnce => buffer += "?",
                CountModifier::Exact(n) => buffer += &format!("^{n}"),
                CountModifier::Range(r) => buffer += &format!("^{{{0}-{1}}}", r.start, r.end),
            },
        }
    }

    buffer
}

#[cfg(test)]
mod tests {
    use crate::parse::parse;
    use crate::postfix::{postfix, postfix_to_string};

    #[test]
    fn test_postfix_simple() {
        let expr = parse("a(bb)+a").unwrap();
        let postfix = postfix(&expr);
        let postfix_str = postfix_to_string(&postfix);

        assert_eq!(postfix_str, "abb.+.a.")
    }

    #[test]
    fn test_simple_letter() {
        let expr = parse("a?a?aa").unwrap();
        let postfix = postfix(&expr);
        let postfix_str = postfix_to_string(&postfix);

        assert_eq!(postfix_str, "a?a?.a.a.");
    }
}
