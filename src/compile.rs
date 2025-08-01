use crate::parse::{Ast, CountModifier};
use std::cell::OnceCell;
use std::collections::{HashMap, HashSet};
use std::rc::{Rc, Weak};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum CompilationError {
    #[error("Missing a fragment, cannot create a concat.")]
    MissingFragment,
    #[error("Bad lookup for node id {0}")]
    BadLookup(usize),
    #[error("Invalid node type, expected single output for node id {0}")]
    ExpectedSingleOutput(usize),
    #[error("Invalid node type, expected choice output for node id {0}")]
    ExpectedChoiceOutput(usize),
    #[error("Node {0} has a double-set output")]
    DoubleSetOutput(usize),
    #[error("Incomplete postfix expression, expected a single node, found {0}")]
    InvalidPostfix(usize),
    #[error("Node with id {0} does not exist in the table")]
    MissingNode(usize),
}

pub type CompilationResult<T> = Result<T, CompilationError>;
type NodeTable = HashMap<usize, Rc<Node>>;

#[derive(Debug)]
pub enum Node {
    LiteralMatch {
        id: usize,
        value: char,
        next: OnceCell<Weak<Node>>,
    },
    AnyMatch {
        id: usize,
        next: OnceCell<Weak<Node>>,
    },
    CharsetMatch {
        id: usize,
        charset: HashSet<char>,
        next: OnceCell<Weak<Node>>,
    },
    Choice {
        id: usize,
        outs: [OnceCell<Weak<Node>>; 2],
    },
    Matching {
        id: usize,
    },
}

impl Node {
    pub fn id(&self) -> usize {
        *match self {
            Node::LiteralMatch { id, .. } => id,
            Node::CharsetMatch { id, .. } => id,
            Node::Choice { id, .. } => id,
            Node::Matching { id, .. } => id,
            Node::AnyMatch { id, .. } => id,
        }
    }
}

pub struct GregExp {
    pub node_table: NodeTable,
    pub start_node_id: usize,
}

#[derive(Debug)]
enum NodeOutput {
    /// The output is the only output of that node
    Simple(usize),
    /// The first integer is the node id, the second the output #
    Choice(usize, usize),
}

#[derive(Debug)]
struct Fragment {
    /// Contains the start node of this fragment
    node: Rc<Node>,
    /// Contains the output(s) of the current fragment that are unbound
    outputs: Vec<NodeOutput>,
}
fn compile_character(
    value: char,
    node_table: &mut NodeTable,
    stack: &mut Vec<Fragment>,
    next_id: &mut usize,
) {
    let node = Rc::new(Node::LiteralMatch {
        id: *next_id,
        value,
        next: OnceCell::new(),
    });

    node_table.insert(*next_id, node.clone());

    stack.push(Fragment {
        node,
        outputs: vec![NodeOutput::Simple(*next_id)],
    });

    *next_id += 1;
}

fn compile_any_match(node_table: &mut NodeTable, stack: &mut Vec<Fragment>, next_id: &mut usize) {
    let node = Rc::new(Node::AnyMatch {
        id: *next_id,
        next: OnceCell::new(),
    });

    node_table.insert(*next_id, node.clone());

    stack.push(Fragment {
        node,
        outputs: vec![NodeOutput::Simple(*next_id)],
    });

    *next_id += 1;
}

fn compile_charset(
    charset: HashSet<char>,
    node_table: &mut NodeTable,
    stack: &mut Vec<Fragment>,
    next_id: &mut usize,
) {
    let node = Rc::new(Node::CharsetMatch {
        id: *next_id,
        charset,
        next: OnceCell::new(),
    });

    node_table.insert(*next_id, node.clone());

    stack.push(Fragment {
        node,
        outputs: vec![NodeOutput::Simple(*next_id)],
    });

    *next_id += 1;
}

/// Link a fragment to the given node.
fn attach_all(from: &Fragment, to: &Rc<Node>, node_table: &NodeTable) -> CompilationResult<()> {
    for output in from.outputs.iter() {
        match output {
            NodeOutput::Simple(node_id) => {
                let node = node_table
                    .get(node_id)
                    .ok_or(CompilationError::BadLookup(*node_id))?;

                match node.as_ref() {
                    Node::LiteralMatch { next, .. }
                    | Node::CharsetMatch { next, .. }
                    | Node::AnyMatch { next, .. } => {
                        next.set(Rc::downgrade(to))
                            .map_err(|_| CompilationError::DoubleSetOutput(*node_id))?;
                    }
                    Node::Choice { .. } | Node::Matching { .. } => {
                        Err(CompilationError::ExpectedSingleOutput(*node_id))?;
                    }
                }
            }
            NodeOutput::Choice(node_id, output_no) => {
                let node = node_table
                    .get(node_id)
                    .ok_or(CompilationError::BadLookup(*node_id))?;

                match node.as_ref() {
                    Node::Choice { outs: out, .. } => {
                        out[*output_no]
                            .set(Rc::downgrade(to))
                            .map_err(|_| CompilationError::DoubleSetOutput(*node_id))?;
                    }
                    Node::LiteralMatch { .. }
                    | Node::CharsetMatch { .. }
                    | Node::AnyMatch { .. }
                    | Node::Matching { .. } => {
                        Err(CompilationError::ExpectedChoiceOutput(*node_id))?;
                    }
                }
            }
        }
    }

    Ok(())
}

fn compile_concat(node_table: &NodeTable, stack: &mut Vec<Fragment>) -> CompilationResult<()> {
    // [ e1, e2 ] (stack)
    let e2 = stack.pop().ok_or(CompilationError::MissingFragment)?;
    let e1 = stack.pop().ok_or(CompilationError::MissingFragment)?;

    attach_all(&e1, &e2.node, node_table)?;

    stack.push(Fragment {
        node: e1.node,
        outputs: e2.outputs,
    });

    Ok(())
}

/// Creates an "or" relation between two fragments
fn compile_or(
    node_table: &mut NodeTable,
    stack: &mut Vec<Fragment>,
    next_id: &mut usize,
) -> CompilationResult<()> {
    // [ e1, e2 ] (stack)
    let e2 = stack.pop().ok_or(CompilationError::MissingFragment)?;
    let e1 = stack.pop().ok_or(CompilationError::MissingFragment)?;

    //     /--- e1 --- (out1)
    // -> <c
    //     \--- e2 --- (out2)

    let node = Rc::new(Node::Choice {
        id: *next_id,
        outs: [
            OnceCell::from(Rc::downgrade(&e1.node)),
            OnceCell::from(Rc::downgrade(&e2.node)),
        ],
    });
    node_table.insert(*next_id, node.clone());

    let mut outputs = Vec::with_capacity(e1.outputs.len() + e2.outputs.len());
    outputs.extend(e1.outputs);
    outputs.extend(e2.outputs);

    stack.push(Fragment { node, outputs });

    *next_id += 1;
    Ok(())
}

fn compile_at_least_once(
    node_table: &mut NodeTable,
    stack: &mut Vec<Fragment>,
    next_id: &mut usize,
) -> CompilationResult<()> {
    // -> e -> c ->
    //    |    |
    //    ^ - -v

    let e = stack.pop().ok_or(CompilationError::MissingFragment)?;

    let node = Rc::new(Node::Choice {
        id: *next_id,
        outs: [OnceCell::from(Rc::downgrade(&e.node)), OnceCell::new()],
    });
    node_table.insert(*next_id, node.clone());
    attach_all(&e, &node, node_table)?;

    // Start is the expr, output is the first node
    stack.push(Fragment {
        node: e.node,
        outputs: vec![NodeOutput::Choice(*next_id, 1)],
    });

    *next_id += 1;
    Ok(())
}

fn compile_star(
    node_table: &mut NodeTable,
    stack: &mut Vec<Fragment>,
    next_id: &mut usize,
) -> CompilationResult<()> {
    //    / --------\
    //    v         |
    // -> c -> e -> /
    //    |
    //    v-------------
    let e = stack.pop().ok_or(CompilationError::MissingFragment)?;

    let choice = Rc::new(Node::Choice {
        id: *next_id,
        outs: [OnceCell::from(Rc::downgrade(&e.node)), OnceCell::new()],
    });
    node_table.insert(*next_id, choice.clone());

    // Attach e back to the choice
    attach_all(&e, &choice, node_table)?;

    // Start is the choice, output is the second node of choice
    stack.push(Fragment {
        node: choice,
        outputs: vec![NodeOutput::Choice(*next_id, 1)],
    });

    *next_id += 1;
    Ok(())
}

fn compile_at_most_once(
    node_table: &mut NodeTable,
    stack: &mut Vec<Fragment>,
    next_id: &mut usize,
) -> CompilationResult<()> {
    let e = stack.pop().ok_or(CompilationError::MissingFragment)?;

    let node = Rc::new(Node::Choice {
        id: *next_id,
        outs: [OnceCell::from(Rc::downgrade(&e.node)), OnceCell::new()],
    });

    node_table.insert(*next_id, node.clone());

    let mut outputs = vec![];
    outputs.extend(e.outputs);
    outputs.push(NodeOutput::Choice(*next_id, 1));

    stack.push(Fragment { node, outputs });

    *next_id += 1;

    Ok(())
}

fn attach_matching_node(
    stack: &mut Vec<Fragment>,
    node_table: &mut NodeTable,
    next_id: usize,
) -> CompilationResult<usize> {
    if stack.len() != 1 {
        return Err(CompilationError::InvalidPostfix(stack.len()));
    }

    let last = stack.pop().expect("Safety guarded by previous assertion");

    let matching = Rc::new(Node::Matching { id: next_id });
    node_table.insert(next_id, matching.clone());
    attach_all(&last, &matching, node_table)?;

    Ok(last.node.id())
}

/// Dispatches every element of the Ast, received in postfix order and creates the appropriate node for it.
fn compile_loop(
    stack: &mut Vec<Fragment>,
    node_table: &mut NodeTable,
    next_id: &mut usize,
    traversal: &[Rc<Ast>],
) -> CompilationResult<()> {
    for segment in traversal.iter() {
        match segment.as_ref() {
            Ast::ExactMatch(c) => compile_character(*c, node_table, stack, next_id),
            Ast::Concat(_, _) => compile_concat(node_table, stack)?,
            Ast::Or(_, _) => compile_or(node_table, stack, next_id)?,
            Ast::Repeat(_, CountModifier::AtMostOnce) => {
                compile_at_most_once(node_table, stack, next_id)?
            }
            Ast::Repeat(_, CountModifier::AtLeastOnce) => {
                compile_at_least_once(node_table, stack, next_id)?
            }
            Ast::Repeat(_, CountModifier::Star) => compile_star(node_table, stack, next_id)?,
            Ast::InGroup(charset) => compile_charset(charset.clone(), node_table, stack, next_id),
            Ast::AnyMatch => compile_any_match(node_table, stack, next_id),
            &Ast::Blank => (),
            &Ast::Repeat(_, CountModifier::Exact(_)) | &Ast::Repeat(_, CountModifier::Range(_)) => {
                panic!("Received complex repeat modifiers, should have been simplified");
            }
        }
    }

    Ok(())
}

/// Prefix an expression with an "any match" expression. For example, if you have a compiled
/// expression
// TODO WRITE DOC
pub fn prefix_with_any_match(original: &GregExp) -> CompilationResult<GregExp> {
    let mut node_table = original.node_table.clone();
    let mut next_id = node_table.keys().max().cloned().map(|v| v + 1).unwrap_or(0);
    let mut stack: Vec<Fragment> = vec![];

    let traversal = [
        Rc::new(Ast::AnyMatch),
        Rc::new(Ast::Repeat(Rc::new(Ast::AnyMatch), CountModifier::Star)),
    ];

    compile_loop(&mut stack, &mut node_table, &mut next_id, &traversal)?;

    assert!(
        stack.len() == 1,
        "There should be only a single node on the stack"
    );

    let from = &stack[0];

    let previous_head = node_table
        .get(&original.start_node_id)
        .ok_or(CompilationError::MissingNode(original.start_node_id))?;

    attach_all(from, previous_head, &node_table)?;

    Ok(GregExp {
        node_table,
        start_node_id: from.node.id(),
    })
}

pub fn compile(tree: Rc<Ast>) -> CompilationResult<GregExp> {
    let mut node_table: NodeTable = HashMap::new();
    let mut next_id = 0;

    let mut stack: Vec<Fragment> = Vec::new();
    let mut postfix_traversal: Vec<Rc<Ast>> = Vec::new();
    tree.into_postfix(&mut postfix_traversal);

    compile_loop(
        &mut stack,
        &mut node_table,
        &mut next_id,
        &postfix_traversal,
    )?;

    let start_node_id = attach_matching_node(&mut stack, &mut node_table, next_id)?;

    Ok(GregExp {
        node_table,
        start_node_id,
    })
}

#[allow(unused)]
pub fn compile_to_dot(exp: &GregExp) -> String {
    let mut builder = String::new();
    let nodes = &exp.node_table;

    builder += "digraph Greggex {\n";

    for id in nodes.keys() {
        builder += &format!("\ta{id} [label=\"{id}\"]\n");
    }

    for node in nodes.values() {
        match node.as_ref() {
            Node::LiteralMatch { id, next, value } => {
                let next = next.get().and_then(Weak::upgrade);

                if next.is_none() {
                    panic!("Expected a next link ({id}, {value})");
                }
                let next = next.expect("Expected a next link");
                builder += &format!("\ta{id} -> a{0}[label=\"{value}\"]\n", next.id());
            }
            Node::CharsetMatch { id, next, charset } => {
                let next = next
                    .get()
                    .and_then(Weak::upgrade)
                    .expect("Expected a next link");

                for value in charset {
                    builder += &format!("\ta{id} -> a{0}[label=\"{value}\"]\n", next.id());
                }
            }
            Node::AnyMatch { id, next } => {
                let next = next
                    .get()
                    .and_then(Weak::upgrade)
                    .expect("Expected a next link");

                builder += &format!("\ta{id} -> a{0}[label=\"<any>\"]\n", next.id());
            }
            Node::Choice { id, outs } => {
                for out in outs {
                    match out.get().and_then(Weak::upgrade) {
                        None => continue,
                        Some(next) => {
                            builder += &format!("\ta{id} -> a{0}\n", next.id());
                        }
                    };
                }
            }
            // Never any output
            Node::Matching { .. } => {}
        }
    }

    builder += "}";
    builder
}

#[cfg(test)]
mod tests {
    use crate::{execute, parse::parse};

    use super::{compile, prefix_with_any_match};

    #[test]
    fn test_adding_matchall_prefix() {
        let expr = "hello";
        let tree = parse(expr).unwrap();
        let original = compile(tree).unwrap();
        let prefixed = prefix_with_any_match(&original).unwrap();

        // Positive cases
        assert!(execute("hello", &prefixed));
        assert!(execute("ahello", &prefixed));
        assert!(execute("aahello", &prefixed));

        // Negative cases
        assert!(!execute("aahell", &prefixed));
        assert!(!execute("aahellxx", &prefixed));
    }
}
