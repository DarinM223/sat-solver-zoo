use sat_solver_zoo::{Formula, cdcl_solve};
use std::{error::Error, fs::File, io::Read};

fn main() -> Result<(), Box<dyn Error>> {
    let args = std::env::args();
    for arg in args.into_iter().skip(1) {
        println!("File: {arg}");
        let mut cnf_file = File::open(arg)?;
        let mut contents = String::new();
        cnf_file.read_to_string(&mut contents)?;
        let mut formula = Formula::from_dimacs_cnf(&contents);
        let Some(assignments) = cdcl_solve(&mut formula) else {
            println!("No assignments found");
            continue;
        };
        println!("Assignment satisfied: {}", assignments.satisfy(&formula));
        for var in formula.vars() {
            let Some(assigned) = assignments.value_var(*var) else {
                continue;
            };
            println!("Assigned {} -> {}", var, assigned);
        }
    }
    Ok(())
}
