#![feature(test)]
extern crate test;

use sat_solver_zoo::{Formula, cdcl_solve};

#[bench]
fn bench_large_cnf(b: &mut test::Bencher) {
    let dimacs = make_large_cnf(40_000);

    b.iter(|| {
        let mut formula = Formula::from_dimacs_cnf(std::hint::black_box(&dimacs));
        let result = cdcl_solve(&mut formula).expect("generated CNF should be SAT");
        std::hint::black_box(result);
    });
}

fn make_large_cnf(vars: usize) -> String {
    use std::fmt::Write;
    let mut dimacs = String::with_capacity(vars * 24);
    writeln!(&mut dimacs, "p cnf {vars} {vars}").unwrap();
    writeln!(&mut dimacs, "1 0").unwrap();

    // 1 forces 2, 2 forces 3, and so on, exercising propagation
    // through a large set of binary clauses.
    for var in 1..vars {
        writeln!(&mut dimacs, "-{var} {} 0", var + 1).unwrap();
    }
    dimacs
}
