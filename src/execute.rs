use crate::compile::{CompiledGreggex, State};
use std::collections::HashSet;
use std::rc::Rc;

fn step(c: Option<char>, state: Rc<State>, future: &mut HashSet<Rc<State>>) {
    if let Some(c) = c {
        if let Some(out) = state.out.get() {
            if state.out_chars.borrow().contains(&c) {
                future.insert(Rc::clone(out));
            }
        }

        if let Some(out) = state.back_out.get() {
            if state.back_chars.borrow().contains(&c) {
                future.insert(Rc::clone(
                    &out.upgrade().expect("The reference should still be valid"),
                ));
            }
        }
    } else {
        future.insert(Rc::clone(&state));
    }

    if let Some(out) = state.free_out.get() {
        future.insert(Rc::clone(&out));
        step(c, Rc::clone(out), future);
    }
}

pub fn execute(input: &str, fsm: &CompiledGreggex) -> bool {
    let (start, end) = fsm;

    let mut current: HashSet<Rc<State>> = HashSet::new();
    current.insert(start.clone());

    let mut future: HashSet<Rc<State>> = HashSet::new();

    for ch in input.chars().map(Some).chain(std::iter::once(None)) {
        for state in &current {
            step(ch, Rc::clone(state), &mut future);
        }

        current.drain();
        for fut in future.drain() {
            current.insert(fut);
        }
    }

    current.contains(end)
}

#[cfg(test)]
mod tests {
    use crate::compile::compile;
    use crate::execute::execute;
    use crate::parse::parse;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn test_simple_string() {
        let parsed = parse("hello-world!").unwrap();
        let compiled = compile(&parsed);
        assert!(execute("hello-world!", &compiled));
        assert!(!execute("hello-there!", &compiled));
    }

    #[test]
    fn test_repeat_group() {
        let parsed = parse("prefix:(hello)*").unwrap();
        let compiled = compile(&parsed);

        assert!(execute("prefix:hello", &compiled));
        assert!(execute("prefix:hellohello", &compiled));
        assert!(execute("prefix:", &compiled));
        assert!(!execute("prefix:nothello", &compiled));
    }

    fn build_hard_input(n: usize) -> String {
        (0..n).map(|_| "a").collect::<Vec<_>>().join("")
    }

    fn build_hard_regex(n: usize) -> String {
        let mut builder = String::new();

        for _ in 0..n {
            builder += "a?";
        }

        for _ in 0..n {
            builder += "a";
        }

        builder
    }

    #[test]
    fn test_hard_regex() {
        const REPEATS: usize = 10;
        const MAX_LEN: usize = 30;

        let mut timings = [0; MAX_LEN];

        for n in 1..=MAX_LEN {
            let regex = build_hard_regex(n);
            let input = build_hard_input(n);
            let parsed = parse(&regex).expect("Should be a valid regex");
            let compiled = compile(&parsed);

            // Run 10 times to average out
            for _ in 0..REPEATS {
                let start = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();
                assert!(execute(&input, &compiled));
                let end = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();
                timings[n - 1] = (end - start).as_nanos()
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

        println!("Min timing: {min}ns");
        println!("Max timing: {max}ns");
    }
}
