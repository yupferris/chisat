#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

pub mod dimacs_cnf;
pub mod ir;
pub mod solvers;

pub use ir::*;
