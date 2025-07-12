use crate::compile::{compile, compile_to_dot};
use crate::execute::execute;
use crate::parse::parse;
use crate::postfix::{postfix, postfix_to_string};

mod compile;
mod execute;
mod parse;
mod postfix;

pub fn matches(input: &str, expr: &str) -> bool {
    let parsed = parse(expr).unwrap();
    let post = postfix(&parsed);
    let compiled = compile(&post).unwrap();
    execute(input, &compiled)
}
