#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

pub mod solvers;

use std::collections::HashMap;
use std::convert::identity;
use std::fmt;
use std::hash::Hash;
use std::ops::Neg;

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct Variable(pub u32);

impl fmt::Debug for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", self.0)?;

        Ok(())
    }
}

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
pub struct Literal {
    pub variable: Variable,
    pub is_positive: bool,
}

impl Literal {
    fn evaluate(&self, assignment: &Assignment) -> bool {
        assignment.values.get(&self.variable).map(|&value| value ^ !self.is_positive).unwrap_or(false)
    }
}

impl fmt::Debug for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        if !self.is_positive {
            write!(f, "-")?;
        }
        write!(f, "{:?}", self.variable)?;

        Ok(())
    }
}

impl Neg for Literal {
    type Output = Literal;

    fn neg(self) -> Self::Output {
        Literal {
            is_positive: !self.is_positive,
            ..self
        }
    }
}

#[derive(Clone)]
pub struct Clause {
    pub literals: Vec<Literal>,
}

impl Clause {
    fn evaluate(&self, assignment: &Assignment) -> bool {
        self.literals.iter().map(|literal| literal.evaluate(assignment)).reduce(|a, b| a || b).unwrap_or(false)
    }

    fn is_empty(&self) -> bool {
        self.literals.is_empty()
    }
}

impl fmt::Debug for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        for (i, literal) in self.literals.iter().enumerate() {
            if i != 0 {
                write!(f, " ")?;
            }
            write!(f, "{:?}", literal)?;
        }

        Ok(())
    }
}

#[derive(Clone)]
pub struct Formula {
    pub clauses: Vec<Clause>,
}

impl Formula {
    fn assign(&self, variable: Variable, value: bool) -> Formula {
        Formula {
            clauses: self.clauses.iter().filter_map(|clause| {
                if clause.literals.contains(&Literal {
                    variable,
                    is_positive: value,
                }) {
                    return None;
                }

                Some(Clause {
                    literals: clause.literals.iter().copied().filter(|&literal| literal != Literal {
                        variable,
                        is_positive: !value,
                    }).collect(),
                })
            }).collect(),
        }
    }

    pub fn evaluate(&self, assignment: &Assignment) -> bool {
        self.clauses.iter().map(|clause| clause.evaluate(assignment)).reduce(|a, b| a && b).unwrap_or(true)
    }

    fn first_pure_literal(&self) -> Option<Literal> {
        let mut variable_map: HashMap<Variable, Option<Literal>> = HashMap::new();
        for clause in &self.clauses {
            for literal in &clause.literals {
                let variable = literal.variable;
                if let Some(prev_literal) = variable_map.get_mut(&variable) {
                    if let Some(prev_literal_value) = prev_literal {
                        if literal.is_positive != prev_literal_value.is_positive {
                            *prev_literal = None;
                        }
                    }
                } else {
                    variable_map.insert(variable, Some(*literal));
                }
            }
        }

        variable_map.values().copied().find_map(identity)
    }

    fn first_unassigned_variable(&self, assignment: &Assignment) -> Option<Variable> {
        self.clauses.iter().find_map(|clause| clause.literals.iter().find_map(|literal| {
            let variable = literal.variable;
            if !assignment.values.contains_key(&variable) {
                Some(variable)
            } else {
                None
            }
        }))
    }

    fn first_unit_clause_literal(&self) -> Option<Literal> {
        for clause in &self.clauses {
            if clause.literals.len() == 1 {
                return Some(clause.literals[0]);
            }
        }

        None
    }
}

impl fmt::Debug for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        writeln!(f)?;
        for clause in &self.clauses {
            writeln!(f, "{:?}", clause)?;
        }

        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct Assignment {
    pub values: HashMap<Variable, bool>,
}

impl Assignment {
    fn assign(&self, variable: Variable, value: bool) -> Assignment {
        let mut ret = self.clone();
        ret.values.insert(variable, value);
        ret
    }

    fn empty() -> Assignment {
        Assignment {
            values: HashMap::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ARBITRARY_NUM_VARIABLES: u32 = 8;

    impl quickcheck::Arbitrary for Variable {
        fn arbitrary(g: &mut quickcheck::Gen) -> Self {
            Variable(u32::arbitrary(g) % ARBITRARY_NUM_VARIABLES)
        }
    }

    impl quickcheck::Arbitrary for Literal {
        fn arbitrary(g: &mut quickcheck::Gen) -> Self {
            Literal {
                variable: Variable::arbitrary(g),
                is_positive: bool::arbitrary(g),
            }
        }
    }

    impl quickcheck::Arbitrary for Clause {
        fn arbitrary(g: &mut quickcheck::Gen) -> Self {
            let max_num_literals = 4;
            // TODO: This excludes 0, which typically results in more interesting formulas,
            //  since any empty clause renders the entire formula unsatisfiable. However,
            //  this may be an important case to check, so we may want to come up with a way
            //  to conditionally include empty clauses with low probability of occurrence.
            let num_literals = (u32::arbitrary(g) % max_num_literals) + 1;
            Clause {
                literals: (0..num_literals).map(|_| Literal::arbitrary(g)).collect(),
            }
        }
    }

    impl quickcheck::Arbitrary for Formula {
        fn arbitrary(g: &mut quickcheck::Gen) -> Self {
            // TODO: Find a good way to respect size that doesn't end up generating too many
            //  unsatisfiable formulas
            let num_clauses = 4;//g.size();
            Formula {
                clauses: (0..num_clauses).map(|_| Clause::arbitrary(g)).collect(),
            }
        }
    }
}
