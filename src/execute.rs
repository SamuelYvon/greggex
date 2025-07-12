use crate::compile::{Gregexp, Node};
use std::cell::OnceCell;
use std::collections::HashSet;
use std::rc::{Rc, Weak};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ExecutionError {}

fn add_node(node: &OnceCell<Weak<Node>>, future: &mut HashSet<usize>) {
    let node = match node.get().map(Weak::upgrade).flatten() {
        Some(node) => node,
        None => return,
    };

    let node_id = node.id();

    if future.contains(&node_id) {
        return;
    }

    match node.as_ref() {
        Node::LiteralMatch { id, .. } => {
            future.insert(*id);
        }
        Node::Choice { outs: out, .. } => {
            add_node(&out[0], future);
            add_node(&out[1], future);
        }
        Node::Matching { id } => {
            future.insert(*id);
        }
    }
}

pub fn execute(input: &str, gregexp: &Gregexp) -> bool {
    let mut current: HashSet<usize> = HashSet::new();
    let mut future: HashSet<usize> = HashSet::new();

    let first_node = gregexp
        .node_table
        .get(&gregexp.start_node_id)
        .map(Rc::downgrade)
        .map(OnceCell::from)
        .expect("The initial node should exist");

    // Every node that is reachable by the first node should be considered.
    add_node(&first_node, &mut current);

    // Also consider the start node itself
    current.insert(gregexp.start_node_id);

    for current_char in input.chars() {
        for current in current.iter().filter_map(|id| gregexp.node_table.get(id)) {
            match current.as_ref() {
                Node::LiteralMatch {
                    value: matching,
                    next,
                    ..
                } => {
                    if *matching == current_char {
                        add_node(&next, &mut future);
                    }
                }
                Node::Choice { .. } => continue,
                Node::Matching { .. } => continue,
            }
        }

        current.clear();
        for node in future.drain() {
            current.insert(node);
        }
    }

    current
        .iter()
        .filter_map(|id| gregexp.node_table.get(id))
        .any(|node| matches!(node.as_ref(), Node::Matching { .. }))
}

#[cfg(test)]
mod tests {
    use crate::compile::{Gregexp, compile, compile_to_dot};
    use crate::execute::execute;
    use crate::parse::parse;
    use crate::postfix::{postfix, postfix_to_string};
    use std::time::{SystemTime, UNIX_EPOCH};

    fn _compile(expr: &str) -> Gregexp {
        let parsed = parse(expr).unwrap();
        let postfixd = postfix(&parsed);

        println!("Postfix: {0}", postfix_to_string(&postfixd));

        let compiled = compile(&postfixd).unwrap();

        println!("{0}", compile_to_dot(&compiled));

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

        for (i, v) in timings.into_iter().enumerate() {
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
}
