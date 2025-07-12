use crate::parse::{CountModifier, Gregexp};
use std::cell::{OnceCell, RefCell};
use std::collections::HashSet;
use std::hash::{Hash, Hasher};
use std::rc::{Rc, Weak};
use thiserror::Error;

const START_STATE_ID: usize = 0;

#[derive(Debug)]
pub struct State {
    pub id: usize,
    pub out: OnceCell<Rc<State>>,
    pub back_out: OnceCell<Weak<State>>,
    pub free_out: OnceCell<Rc<State>>,
    pub out_chars: RefCell<HashSet<char>>,
    pub back_chars: RefCell<HashSet<char>>,
}

impl Eq for State {}

impl PartialEq for State {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Hash for State {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.id.hash(hasher);
    }
}

pub type CompiledGreggex = (Rc<State>, Rc<State>);

impl State {
    fn new(id: usize) -> Rc<Self> {
        Rc::new(State {
            id,
            out: OnceCell::new(),
            out_chars: RefCell::new(HashSet::new()),
            free_out: OnceCell::new(),
            back_out: OnceCell::new(),
            back_chars: RefCell::new(HashSet::new()),
        })
    }
}

#[derive(Debug, Error, Eq, PartialEq, Clone)]
pub enum CompilationError {}

fn compile_group(
    previous: Rc<State>,
    gregexp: &Rc<Gregexp>,
    modifier: Option<CountModifier>,
) -> Rc<State> {
    match modifier {
        None => compile_any(previous, gregexp),
        // {*}
        Some(CountModifier::Star) => {
            let group = compile_any(previous.clone(), gregexp);
            let free_node = State::new(group.id + 1);

            let first_of_group = previous
                .out
                .get()
                .expect("Should have been set, a group has been generated.");

            // The end of the group can link back to the start of the group, based
            // on the same criteria
            group
                .back_out
                .set(Rc::downgrade(&first_of_group))
                .expect("Should never have been set");
            // Add the criteria
            for entry in previous.out_chars.borrow().iter() {
                group.back_chars.borrow_mut().insert(*entry);
            }

            group
                .free_out
                .set(free_node.clone())
                .expect("Should never have been set");

            previous
                .free_out
                .set(free_node.clone())
                .expect("Should never have been set");

            free_node
        }
        // +
        Some(CountModifier::AtLeastOnce) => {
            let group = compile_any(previous.clone(), gregexp);
            let free_node = State::new(group.id + 1);

            let first_of_group = previous
                .out
                .get()
                .expect("Should have been set, a group has been generated.");

            // The end of the group can link back to the start of the group, based
            // on the same criteria
            group
                .back_out
                .set(Rc::downgrade(&first_of_group))
                .expect("Should never have been set");
            // Add the criteria
            for entry in previous.out_chars.borrow().iter() {
                group.back_chars.borrow_mut().insert(*entry);
            }

            group
                .free_out
                .set(free_node.clone())
                .expect("Should never have been set");

            free_node
        }
        // {?}
        Some(CountModifier::AtMostOnce) => {
            let group = compile_any(previous.clone(), gregexp);
            let free_node = State::new(group.id + 1);

            previous
                .free_out
                .set(free_node.clone())
                .expect("Should never have been set");

            group
                .free_out
                .set(free_node.clone())
                .expect("Should never have been set");

            free_node
        }
        // {n}
        Some(CountModifier::Exact(n)) => {
            let mut previous = previous;

            for _ in 0..n {
                previous = compile_any(previous, gregexp);
            }

            previous
        }
        Some(_) => {
            todo!()
        }
    }
}

fn compile_exact_match(previous: Rc<State>, c: char, modifier: Option<CountModifier>) -> Rc<State> {
    match modifier {
        None => {
            let node = State::new(previous.id + 1);

            // We make the link between the previous node and here. The real
            // owner is now previous.
            previous
                .out
                .set(node.clone())
                .expect("Should never have been set before!");
            previous.out_chars.borrow_mut().insert(c);

            node
        }
        // +
        Some(CountModifier::AtLeastOnce) => {
            let node = State::new(previous.id + 1);

            previous
                .out
                .set(node.clone())
                .expect("Should never have been set before!");
            previous.out_chars.borrow_mut().insert(c);

            node.back_out
                .set(Rc::downgrade(&node))
                .expect("Should never have been set before!");

            node.back_chars.borrow_mut().insert(c);

            node
        }
        // ?
        Some(CountModifier::AtMostOnce) => {
            let node = State::new(previous.id + 1);
            // let free_node = State::new(node.id + 1);

            previous
                .out
                .set(node.clone())
                .expect("Should never have been set before!");
            previous.out_chars.borrow_mut().insert(c);

            // node.free_out
            //     .set(free_node.clone())
            //     .expect("Should never have been set before!");

            previous
                .free_out
                .set(node.clone())
                .expect("Should never have been set before!");

            node
        }
        // *
        Some(CountModifier::Star) => {
            let node = State::new(previous.id + 1);
            let exit_node = State::new(node.id + 1);

            // Can repeat into itself
            node.back_out
                .set(Rc::downgrade(&node))
                .expect("Should never have been set before!");
            node.back_chars.borrow_mut().insert(c);

            // Can "escape" through the free node
            node.free_out
                .set(exit_node.clone())
                .expect("Should never have been set before!");

            // Can go to the new node through the planned path
            previous
                .out
                .set(node.clone())
                .expect("Should never have been set before!");
            previous.out_chars.borrow_mut().insert(c);

            // Can escape through the exit node
            previous
                .free_out
                .set(exit_node.clone())
                .expect("Should never have been set before!");

            exit_node
        }
        // {n}
        Some(CountModifier::Exact(n)) => {
            let mut previous = previous;

            for _ in 0..n {
                let node = State::new(previous.id + 1);

                previous
                    .out
                    .set(node.clone())
                    .expect("Should never have been set before!");
                previous.out_chars.borrow_mut().insert(c);

                previous = node
            }

            previous
        }
        _ => todo!(),
    }
}

/// Compile a sequence
fn compile_sequence(previous: Rc<State>, exprs: &Vec<Gregexp>) -> Rc<State> {
    let mut previous = previous;

    for expr in exprs {
        previous = compile_any(previous, expr);
    }

    previous
}

/// Given the start node, generate the dot representation of the FSM
fn to_dot(start_node: Rc<State>) -> String {
    let mut result = String::new();
    result += "digraph fsm {\n";

    let mut dfs = vec![start_node.clone()];

    while let Some(node) = dfs.pop() {
        let id = node.id;
        result += &format!("\ta{id} [label=\"{id}\"]\n");

        if let Some(state) = node.out.get().cloned() {
            dfs.push(state);
        }

        if let Some(state) = node.free_out.get().cloned() {
            dfs.push(state);
        }
    }

    dfs.clear();
    dfs = vec![start_node.clone()];

    while let Some(node) = dfs.pop() {
        let id0 = node.id;

        if let Some(other) = node.out.get() {
            let id1 = other.id;
            let chars = node
                .out_chars
                .borrow()
                .iter()
                .map(|c| c.to_string())
                .collect::<Vec<String>>()
                .join(",");

            result += &format!("\ta{id0} -> a{id1} [label=\"{chars}\"]\n");
        }

        if let Some(other) = node.back_out.get() {
            let id1 = other
                .upgrade()
                .expect("The back ref should still be a valid reference")
                .id;
            let chars = node
                .back_chars
                .borrow()
                .iter()
                .map(|c| c.to_string())
                .collect::<Vec<String>>()
                .join(",");

            result += &format!("\ta{id0} -> a{id1} [label=\"{chars}\"]\n");
        }

        if let Some(other) = node.free_out.get() {
            let id1 = other.id;
            result += &format!("\ta{id0} -> a{id1}\n");
        }

        if let Some(state) = node.out.get().cloned() {
            dfs.push(state);
        }

        if let Some(state) = node.free_out.get().cloned() {
            dfs.push(state);
        }
    }

    result += "};";

    result
}

fn compile_any(previous: Rc<State>, gregexp: &Gregexp) -> Rc<State> {
    match gregexp {
        Gregexp::Sequence(exprs) => compile_sequence(previous, exprs),
        Gregexp::Group(expr, modifier) => compile_group(previous, expr, modifier.clone()),
        Gregexp::CharacterGroup(_) => todo!(),
        Gregexp::ExactMatch(c, modifier) => compile_exact_match(previous, *c, modifier.clone()),
    }
}

pub fn compile(gregexp: &Gregexp) -> CompiledGreggex {
    let start_node = State::new(START_STATE_ID);
    let last_node = compile_any(start_node.clone(), gregexp);

    println!("{0}\n", to_dot(start_node.clone()));

    (start_node, last_node)
}

#[cfg(test)]
mod tests {
    use crate::compile::{
        START_STATE_ID, State, compile, compile_any, compile_exact_match, to_dot,
    };
    use crate::parse::{CountModifier, Gregexp, parse};
    use std::rc::Rc;

    #[test]
    fn simple_a_match() {
        let start_node = State::new(START_STATE_ID);
        compile_exact_match(start_node.clone(), 'A', None);
        println!("{0}", to_dot(start_node));
    }

    #[test]
    fn simple_a_plus_match() {
        let start_node = State::new(START_STATE_ID);
        compile_exact_match(start_node.clone(), 'A', Some(CountModifier::AtLeastOnce));
        println!("{0}", to_dot(start_node));
    }

    #[test]
    fn simple_a_quest_match() {
        let start_node = State::new(START_STATE_ID);
        compile_exact_match(start_node.clone(), 'A', Some(CountModifier::AtMostOnce));
        println!("{0}", to_dot(start_node));
    }

    #[test]
    fn simple_a_star_match() {
        let start_node = State::new(START_STATE_ID);
        compile_exact_match(start_node.clone(), 'A', Some(CountModifier::Star));
        println!("{0}", to_dot(start_node));
    }

    #[test]
    fn simple_a_4_match() {
        let start_node = State::new(START_STATE_ID);
        compile_exact_match(start_node.clone(), 'A', Some(CountModifier::Exact(4)));
        println!("{0}", to_dot(start_node));
    }

    #[test]
    fn simple_ab_match() {
        let start_node = State::new(START_STATE_ID);

        compile_any(
            start_node.clone(),
            &Gregexp::Sequence(vec![
                Gregexp::ExactMatch('A', None),
                Gregexp::ExactMatch('B', None),
            ]),
        );

        println!("{0}", to_dot(start_node));
    }

    #[test]
    fn test_simple_ab_group_repeat() {
        let start_node = State::new(START_STATE_ID);

        let sequence = Gregexp::Sequence(vec![
            Gregexp::ExactMatch('A', None),
            Gregexp::ExactMatch('B', None),
        ]);

        compile_any(
            start_node.clone(),
            &Gregexp::Group(Rc::new(sequence), Some(CountModifier::Exact(2))),
        );

        println!("{0}", to_dot(start_node));
    }

    #[test]
    fn test_simple_ab_group_opt() {
        let start_node = State::new(START_STATE_ID);

        let sequence = Gregexp::Sequence(vec![
            Gregexp::ExactMatch('A', None),
            Gregexp::ExactMatch('B', None),
        ]);

        compile_any(
            start_node.clone(),
            &Gregexp::Group(Rc::new(sequence), Some(CountModifier::AtMostOnce)),
        );

        println!("{0}", to_dot(start_node));
    }

    #[test]
    fn test_simple_abc_group_star() {
        let start_node = State::new(START_STATE_ID);

        let sequence = Gregexp::Sequence(vec![
            Gregexp::ExactMatch('A', None),
            Gregexp::ExactMatch('B', None),
            Gregexp::ExactMatch('C', None),
        ]);

        compile_any(
            start_node.clone(),
            &Gregexp::Group(Rc::new(sequence), Some(CountModifier::Star)),
        );

        println!("{0}", to_dot(start_node));
    }

    #[test]
    fn test_simple_abc_group_at_least_once() {
        let start_node = State::new(START_STATE_ID);

        let sequence = Gregexp::Sequence(vec![
            Gregexp::ExactMatch('A', None),
            Gregexp::ExactMatch('B', None),
            Gregexp::ExactMatch('C', None),
        ]);

        compile_any(
            start_node.clone(),
            &Gregexp::Group(Rc::new(sequence), Some(CountModifier::AtLeastOnce)),
        );

        println!("{0}", to_dot(start_node));
    }

    #[test]
    fn test_repeat_with_prefix() {
        let expr = parse("prefix:(hello)*").expect("Should parse successfully");
        let (start, _) = compile(&expr);

        println!("{0}", to_dot(start));
    }
}
