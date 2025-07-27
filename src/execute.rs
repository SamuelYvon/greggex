use crate::compile::{GregExp, Node, prefix_with_any_match};
use std::cell::OnceCell;
use std::char;
use std::collections::HashSet;
use std::rc::{Rc, Weak};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ExecutionError {}

#[derive(Debug, PartialEq, Eq)]
enum StepResult {
    /// Cannot continue, ran out of string to test on
    OutOfInput,
    /// Matched at the given position
    Match { pos: usize },
    /// Can step more
    CanStep,
}

/// The execution state carries information between match iterations
/// and allows step by step execution of the regex.
pub struct ExecutionState<'regex> {
    input: Vec<char>,
    current: HashSet<usize>,
    future: HashSet<usize>,
    gregexp: &'regex GregExp,
    pos: usize,
}

pub struct GregMatches {
    pub substrs: Vec<(usize, usize)>,
}

fn add_node(node: &OnceCell<Weak<Node>>, future: &mut HashSet<usize>, any_match: &mut bool) {
    let node = match node.get().and_then(Weak::upgrade) {
        Some(node) => node,
        None => return,
    };

    let node_id = node.id();

    if future.contains(&node_id) {
        return;
    }

    match node.as_ref() {
        Node::LiteralMatch { id, .. }
        | Node::CharsetMatch { id, .. }
        | Node::AnyMatch { id, .. } => {
            future.insert(*id);
        }
        Node::Choice { outs: out, .. } => {
            add_node(&out[0], future, any_match);
            add_node(&out[1], future, any_match);
        }
        Node::Matching { id } => {
            future.insert(*id);
            *any_match |= true;
        }
    }
}

impl ExecutionState<'_> {
    fn new<'gregexp>(input: &str, gregexp: &'gregexp GregExp) -> ExecutionState<'gregexp> {
        let mut current: HashSet<usize> = HashSet::new();
        let future: HashSet<usize> = HashSet::new();

        let first_node = gregexp
            .node_table
            .get(&gregexp.start_node_id)
            .map(Rc::downgrade)
            .map(OnceCell::from)
            .expect("The initial node should exist");

        // Every node that is reachable by the first node should be considered.
        add_node(&first_node, &mut current, &mut false);

        // Also consider the start node itself
        current.insert(gregexp.start_node_id);

        ExecutionState {
            input: input.chars().collect::<Vec<_>>(),
            current,
            future,
            gregexp,
            pos: 0,
        }
    }

    fn step(&mut self) -> StepResult {
        let current_char = match self.input.get(self.pos) {
            Some(c) => *c,
            None => return StepResult::OutOfInput,
        };

        let mut any_match = false;

        for current in self
            .current
            .iter()
            .filter_map(|id| self.gregexp.node_table.get(id))
        {
            match current.as_ref() {
                Node::LiteralMatch {
                    value: matching,
                    next,
                    ..
                } => {
                    if *matching == current_char {
                        add_node(next, &mut self.future, &mut any_match);
                    }
                }
                Node::CharsetMatch { charset, next, .. } => {
                    if charset.contains(&current_char) {
                        add_node(next, &mut self.future, &mut any_match);
                    }
                }
                Node::AnyMatch { next, .. } => {
                    add_node(next, &mut self.future, &mut any_match);
                }
                Node::Choice { .. } => continue,
                Node::Matching { .. } => any_match = true,
            }
        }

        self.current.clear();
        for node in self.future.drain() {
            self.current.insert(node);
        }

        // Save the pos in case we matched
        let pos = self.pos;

        // Move forward
        self.pos += 1;

        if any_match {
            StepResult::Match { pos }
        } else {
            StepResult::CanStep
        }
    }
}

/// Execute the [GregExp] unto the given string, returning [true] if the string
/// matches the expression.
pub fn execute(input: &str, gregexp: &GregExp) -> bool {
    let mut state = ExecutionState::new(input, gregexp);
    let mut previous_result = StepResult::CanStep;

    loop {
        let result = state.step();

        if result == StepResult::OutOfInput {
            break matches!(previous_result, StepResult::Match { pos: _ });
        } else {
            previous_result = result;
        }
    }
}

/// Returns [true] if the expression can be matched anywhere in the string at least once.
pub fn find_anywhere(input: &str, gregexp: &GregExp) -> bool {
    let gregexp =
        &prefix_with_any_match(gregexp).expect("Should have been able to transform the regex.");

    execute(input, gregexp)
}

/// Find all matches of the expression within the string.
pub fn find_all_matches(input: &str, gregexp: &GregExp) -> GregMatches {
    let gregexp =
        &prefix_with_any_match(gregexp).expect("Should have been able to transform the regex.");

    let mut substrs = vec![];
    let mut match_start = 0;

    let mut state = ExecutionState::new(input, gregexp);
    let mut previous_result = StepResult::CanStep;

    loop {
        let result = state.step();
        match result {
            StepResult::OutOfInput => {
                match previous_result {
                    StepResult::OutOfInput | StepResult::CanStep => (),
                    StepResult::Match { pos } => substrs.push((match_start, pos)),
                }
                break;
            }
            StepResult::Match { pos } => {
                substrs.push((match_start, pos));
                match_start = pos;
                previous_result = StepResult::CanStep;

                // TODO: when we match, we need to reset the execution state at the same place
                // TODO  we would be if we started again
            }
            StepResult::CanStep => (),
        }
    }

    GregMatches { substrs }
}

#[cfg(test)]
mod tests {
    use crate::compile::{GregExp, compile, compile_to_dot};
    use crate::execute::execute;
    use crate::parse::parse;
    use std::fs;
    use std::fs::File;
    use std::io::Write;
    use std::time::{SystemTime, UNIX_EPOCH};

    use super::find_all_matches;

    fn _compile(expr: &str) -> GregExp {
        let parsed = parse(expr).unwrap();
        let compiled = compile(parsed).unwrap();
        let compiled_dot = compile_to_dot(&compiled);
        let _ = fs::create_dir(".out");
        let mut file = File::create(".out/output.dot").expect("");
        file.write_all(compiled_dot.as_bytes())
            .expect("Should be able to write the entirety of the file to disk.");

        compiled
    }

    #[test]
    fn test_simple_regex() {
        let compiled = _compile("abc");
        assert!(execute("abc", &compiled));
    }

    #[test]
    fn test_at_most_once_regex() {
        let compiled = _compile("a?bc");
        assert!(execute("abc", &compiled));
        assert!(execute("bc", &compiled));
    }

    #[test]
    fn test_at_least_once() {
        let compiled = _compile("a+hello");

        assert!(!execute("hello", &compiled));
        assert!(execute("ahello", &compiled));
        assert!(execute("aahello", &compiled));
        assert!(execute("aaahello", &compiled));
    }

    #[test]
    fn test_star() {
        let compiled = _compile("a*hello");

        assert!(execute("hello", &compiled));
        assert!(execute("ahello", &compiled));
        assert!(execute("aahello", &compiled));
        assert!(execute("aaahello", &compiled));
    }

    #[test]
    fn test_char_group_simple() {
        let compiled = _compile("6541[0-9]{12}");
        assert!(execute("6541000011112222", &compiled));
    }

    #[test]
    fn test_diners_club() {
        let compiled = _compile("3(0[0-5]|[68][0-9])[0-9]{11}");
        assert!(execute("30569309025904", &compiled));
        assert!(execute("38520000023237", &compiled));
        assert!(!execute("30620000023237", &compiled));
        assert!(!execute("39520000023237", &compiled));
    }

    #[test]
    fn test_or() {
        let compiled = _compile("([a-z]|[0-9])");
        assert!(execute("a", &compiled));
        assert!(execute("z", &compiled));
        assert!(execute("0", &compiled));
        assert!(execute("9", &compiled));
        assert!(!execute("@", &compiled));
    }

    #[test]
    fn test_multiple_ors() {
        let compiled = _compile("([0-1]|[2-3]|[4-5]|[6-7])");
        assert!(execute("0", &compiled));
        assert!(execute("1", &compiled));
        assert!(execute("2", &compiled));
        assert!(execute("3", &compiled));
        assert!(execute("4", &compiled));
        assert!(execute("5", &compiled));
        assert!(execute("6", &compiled));
        assert!(execute("7", &compiled));
        assert!(!execute("8", &compiled));
        assert!(!execute("9", &compiled));
    }

    #[test]
    fn test_dot() {
        let compiled = _compile("a\\.a");
        assert!(execute("a.a", &compiled));
        assert!(!execute("aaa", &compiled));
    }

    #[test]
    fn a_bad_email_regex() {
        let compiled = _compile(
            "([a-z]|[A-Z]|[0-9]|[\\._%\\+\\-]){1,64}@(([a-z]|[A-Z]|[0-9]){1,63}\\.){1,125}([a-z]|[A-Z]){2,63}",
        );
        assert!(execute("anemail@host.com", &compiled));
    }

    #[test]
    fn test_any_match() {
        let compiled = _compile(".*");

        assert!(execute(".*", &compiled));
        assert!(execute("anything-at-all", &compiled));
        assert!(execute("this does not care", &compiled));
        assert!(execute("what the input is", &compiled));
    }

    fn make_pathlogical_expr(n: usize) -> String {
        let mut builder = String::new();

        for _ in 0..n {
            builder += "a?";
        }

        for _ in 0..n {
            builder += "a";
        }

        builder
    }

    fn make_pathological_ipt(n: usize) -> String {
        (0..n).map(|_| "a").collect::<Vec<_>>().join("")
    }

    #[test]
    fn test_hard_regex() {
        const REPEATS: usize = 10;
        const MAX_LEN: usize = 100;

        let mut timings = [0; MAX_LEN];

        for n in 1..=MAX_LEN {
            let regex = make_pathlogical_expr(n);
            let input = make_pathological_ipt(n);
            let compiled = _compile(&regex);

            // Run 10 times to average out
            for _ in 0..REPEATS {
                let start = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();
                assert!(execute(&input, &compiled));
                let end = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();
                timings[n - 1] = (end - start).as_micros()
            }
        }

        let mut max = 0_u128;
        let mut min = timings[0];

        for v in timings.into_iter() {
            if v > max {
                max = v;
            }
            if v < min {
                min = v;
            }
        }

        println!("Min timing: {min}us");
        println!("Max timing: {max}us");
    }

    #[test]
    fn test_find_all_matches_simple() {
        let expr = "hello";
        let tree = parse(expr).unwrap();
        let gregexp = compile(tree).unwrap();
        let matches = find_all_matches(
            "hello there from the ocean. I say hello!. I said hello!",
            &gregexp,
        );
        dbg!(matches.substrs);
    }
}
