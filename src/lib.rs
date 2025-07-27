use compile::{GregExp, compile_to_dot};
use execute::GregMatches;
use parse::ParsingError;
use thiserror::Error;

use crate::execute::execute;
use crate::parse::parse;

mod compile;
mod execute;
mod lexer;
mod parse;

const COMPILATION_ERROR: &str = "Internal error, failed to compile a valid regex";

#[derive(Error, Debug)]
pub enum GreggexError {
    #[error("Parsing error: {0}")]
    ParsingError(#[from] ParsingError),
}

pub type GreggexResult<T> = Result<T, GreggexError>;

/// Compile an expression into a [GregExp] which can be
/// re-used to match against arbitrary strings.
pub fn compile(expr: &str) -> GreggexResult<GregExp> {
    let parsed = parse(expr)?;
    Ok(compile::compile(parsed).expect(COMPILATION_ERROR))
}

/// One-shot function for matching a string with a regex. Not very fast, since the
/// regex must be re-compiled.
pub fn matches(input: &str, expr: &str) -> GreggexResult<bool> {
    let parsed = parse(expr)?;
    let compiled = compile::compile(parsed).expect(COMPILATION_ERROR);
    Ok(execute(input, &compiled))
}

/// Find all the location in the string where the expression occurs
pub fn find_all_matches(input: &str, expr: &GregExp) -> GregMatches {
    execute::find_all_matches(input, expr)
}

/// Find a match anywhere in the string
pub fn find_anywhere(input: &str, gregexp: &GregExp) -> bool {
    execute::find_anywhere(input, gregexp)
}

/// Compile the expression into a .dot graph. This graph can be exported
/// to be visualized later.
pub fn visualize_dot(expr: &GregExp) -> String {
    compile_to_dot(expr)
}
