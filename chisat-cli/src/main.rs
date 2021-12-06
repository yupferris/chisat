use chisat::*;

use std::env;
use std::fs::File;
use std::io;
use std::time::Instant;

fn main() -> io::Result<()> {
    if env::args().count() < 2 {
        panic!("Missing CNF file name arg(s)");
    }
    for cnf_file_name in env::args().skip(1) {

        let mut formula = Formula::new();

        println!("c parsing file {}", cnf_file_name);
        dimacs_cnf::parse(&mut formula, File::open(cnf_file_name)?)?;
        println!("c parsing successful");
        println!("c {} variable(s), {} clause(s)", formula.num_variables(), formula.num_clauses());

        println!("c solving");
        let start_time = Instant::now();
        let result = solvers::dpll(&formula);
        let elapsed_time = start_time.elapsed();
        let elapsed_time_s = (elapsed_time.as_secs() as f64) + (elapsed_time.subsec_nanos() as f64) / 1000000000.0;
        println!("c solving successful");
        println!("c elapsed time: {:.*}s", 2, elapsed_time_s);
        println!("c {} search steps", result.1);

        match result.0 {
            Some(assignment) => {
                println!("s SATISFIABLE");
                print!("v");
                for (variable, value) in assignment.values {
                    print!(" ");
                    if !value {
                        print!("-");
                    }
                    print!("{}", variable.index() as i32 + 1);
                }
                println!();
            }
            None => {
                println!("s UNSATISFIABLE");
                // TODO: Extract and print proof
            }
        }

        println!("c done");
        println!();
    }

    Ok(())
}
