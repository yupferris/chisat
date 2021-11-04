use std::collections::HashMap;
use std::fmt;
use std::ops::Neg;

#[derive(Clone, Debug)]
struct Variable {
    name: String,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[repr(transparent)]
struct VariableRef(u32);

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Literal {
    Positive(VariableRef),
    Negative(VariableRef),
}

impl Literal {
    fn evaluate(&self, assignment: &Assignment) -> bool {
        let (variable, is_negative) = match self {
            Literal::Positive(variable) => (variable, false),
            Literal::Negative(variable) => (variable, true),
        };
        assignment.values.get(&variable).map(|&value| value ^ is_negative).unwrap_or(false)
    }

    fn variable(&self) -> VariableRef {
        match self {
            &Literal::Positive(variable) => variable,
            &Literal::Negative(variable) => variable,
        }
    }
}

// TODO: Is Not a better choice perhaps?
impl Neg for Literal {
    type Output = Literal;

    fn neg(self) -> Self::Output {
        match self {
            Literal::Positive(variable) => Literal::Negative(variable),
            Literal::Negative(variable) => Literal::Positive(variable),
        }
    }
}

#[derive(Clone, Debug)]
struct Clause {
    literals: Vec<Literal>,
}

impl Clause {
    fn evaluate(&self, assignment: &Assignment) -> bool {
        self.literals.iter().map(|literal| literal.evaluate(assignment)).reduce(|a, b| a || b).unwrap_or(false)
    }
}

#[derive(Clone)]
struct Formula {
    clauses: Vec<Clause>,
}

impl Formula {
    fn evaluate(&self, assignment: &Assignment) -> bool {
        self.clauses.iter().map(|clause| clause.evaluate(assignment)).reduce(|a, b| a && b).unwrap_or(true)
    }

    fn first_pure_literal(&self) -> Option<Literal> {
        let mut literal_map = HashMap::new();
        for clause in &self.clauses {
            for literal in &clause.literals {
                if let Some(is_pure) = literal_map.get_mut(literal) {
                    *is_pure = false;
                } else {
                    literal_map.insert(*literal, true);
                }
            }
        }

        literal_map.into_iter().find_map(|(literal, is_pure)| {
            if is_pure {
                Some(literal)
            } else {
                None
            }
        })
    }

    fn first_unassigned_variable(&self, assignment: &Assignment) -> Option<VariableRef> {
        self.clauses.iter().find_map(|clause| clause.literals.iter().find_map(|literal| {
            let variable = literal.variable();
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

#[derive(Clone)]
struct Instance {
    variables: Vec<Variable>,
    formula: Formula,
}

impl fmt::Debug for Instance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        writeln!(f)?;
        for clause in &self.formula.clauses {
            write!(f, "/\\ (")?;
            for literal in &clause.literals {
                write!(f, "\\/ ")?;
                let (variable, is_negative) = match literal {
                    Literal::Positive(variable) => (variable, false),
                    Literal::Negative(variable) => (variable, true),
                };
                let variable_name = &self.variables[variable.0 as usize].name;
                if is_negative {
                    write!(f, "-")?;
                }
                write!(f, "{}", variable_name)?;
            }
            writeln!(f, ")")?;
        }

        Ok(())
    }
}

#[derive(Clone, Debug)]
struct Assignment {
    values: HashMap<VariableRef, bool>,
}

impl Assignment {
    fn empty() -> Assignment {
        Assignment {
            values: HashMap::new(),
        }
    }

    fn insert_satisfying_assignment(&self, literal: Literal) -> Assignment {
        let mut ret = self.clone();
        let (variable, value) = match literal {
            Literal::Positive(variable) => (variable, true),
            Literal::Negative(variable) => (variable, false),
        };
        ret.values.insert(variable, value);
        ret
    }
}

#[derive(Debug)]
enum Satisfiability {
    Satisfiable(Assignment),
    Unsatisfiable,
}

impl Satisfiability {
    fn is_satisfiable(&self) -> bool {
        match self {
            Satisfiability::Satisfiable(_) => true,
            Satisfiability::Unsatisfiable => false,
        }
    }
}

fn backtracking(formula: &Formula) -> Satisfiability {
    fn go(formula: &Formula, assignment: &Assignment) -> Satisfiability {
        if formula.evaluate(assignment) {
            return Satisfiability::Satisfiable(assignment.clone());
        }
        if let Some(variable) = formula.first_unassigned_variable(assignment) {
            let mut positive_assignment = assignment.clone();
            positive_assignment.values.insert(variable, true);
            let result = go(formula, &positive_assignment);
            if result.is_satisfiable() {
                return result;
            }
            let mut negative_assignment = assignment.clone();
            negative_assignment.values.insert(variable, false);
            let result = go(formula, &negative_assignment);
            if result.is_satisfiable() {
                return result;
            }
        }
        Satisfiability::Unsatisfiable
    }
    go(formula, &Assignment::empty())
}

fn dpll(formula: &Formula) -> Satisfiability {
    fn go(formula: &Formula, assignment: &Assignment) -> Satisfiability {
        if formula.clauses.is_empty() {
            return Satisfiability::Satisfiable(assignment.clone());
        }

        // Unit clause rule
        if let Some(literal) = formula.first_unit_clause_literal() {
            let clauses = formula.clauses.iter().filter_map(|clause| {
                if clause.literals.contains(&literal) {
                    return None;
                }

                let literals = clause.literals.iter().copied().filter(|&l| l != -literal).collect::<Vec<_>>();
                Some(Clause {
                    literals,
                })
            }).collect();
            let assignment = assignment.insert_satisfying_assignment(literal);
            return go(&Formula {
                clauses,
            }, &assignment);
        }

        // Pure literal rule
        if let Some(literal) = formula.first_pure_literal() {
            let clauses = formula.clauses.iter().filter(|clause| {
                !clause.literals.contains(&literal) && !clause.literals.contains(&-literal)
            }).cloned().collect();
            let assignment = assignment.insert_satisfying_assignment(literal);
            return go(&Formula {
                clauses,
            }, &assignment);
        }

        // TODO: Try negative and positive partial assignments

        Satisfiability::Unsatisfiable
    }
    go(formula, &Assignment::empty())
}

fn main() {
    let instance = Instance {
        variables: vec![
            Variable {
                name: "a".into(),
            },
            Variable {
                name: "b".into(),
            },
        ],
        formula: Formula {
            clauses: vec![
                Clause {
                    literals: vec![
                        Literal::Positive(VariableRef(0)),
                    ],
                },
                Clause {
                    literals: vec![
                        Literal::Negative(VariableRef(1)),
                    ],
                },
                Clause {
                    literals: vec![
                        Literal::Positive(VariableRef(1)),
                    ],
                },
            ],
        },
    };

    println!("instance: {:?}", instance);

    let backtracking_result = backtracking(&instance.formula);
    println!("backtracking result: {:?}", backtracking_result);
    if let Satisfiability::Satisfiable(assignment) = &backtracking_result {
        assert!(instance.formula.evaluate(assignment));
    }

    let dpll_result = dpll(&instance.formula);
    println!("DPLL result: {:?}", dpll_result);
    if let Satisfiability::Satisfiable(assignment) = &dpll_result {
        assert!(instance.formula.evaluate(assignment));
    }

    assert_eq!(backtracking_result.is_satisfiable(), dpll_result.is_satisfiable());
}

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

#[cfg(test)]
impl quickcheck::Arbitrary for Instance {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[quickcheck]
    fn backtracking_and_dpll_reach_the_same_conclusion(instance: Instance) -> bool {
        let backtracking_result = backtracking(&instance.formula);
        let dpll_result = dpll(&instance.formula);
        backtracking_result.is_satisfiable() == dpll_result.is_satisfiable()
    }
}
