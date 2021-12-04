use chisat::*;

use std::env;
use std::fs::File;
use std::io;

fn main() -> io::Result<()> {
    let cnf_file_name = env::args().skip(1).next().expect("Missing CNF file name arg");

    let mut formula = Formula::new();

    println!("c parsing file {}", cnf_file_name);
    dimacs::parse(&mut formula, File::open(cnf_file_name)?)?;
    println!("c parsing successful");

    println!("c solving");
    let result = solvers::dpll(&formula);
    println!("c solving successful");
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
        }
        None => {
            println!("s UNSATISFIABLE");
            // TODO: Extract and print proof
        }
    }

    println!("c done");

    Ok(())
}
