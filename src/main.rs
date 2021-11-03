use std::collections::HashMap;
use std::fmt;
use std::ops::Neg;

#[derive(Debug)]
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
        let (variable_ref, is_negative) = match self {
            Literal::Positive(variable_ref) => (variable_ref, false),
            Literal::Negative(variable_ref) => (variable_ref, true),
        };
        assignment.values.get(&variable_ref).map(|&value| value ^ is_negative).unwrap_or(false)
    }
}

// TODO: Is Not a better choice perhaps?
impl Neg for Literal {
    type Output = Literal;

    fn neg(self) -> Self::Output {
        match self {
            Literal::Positive(variable_ref) => Literal::Negative(variable_ref),
            Literal::Negative(variable_ref) => Literal::Positive(variable_ref),
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

struct Formula {
    clauses: Vec<Clause>,
}

impl Formula {
    fn evaluate(&self, assignment: &Assignment) -> bool {
        self.clauses.iter().map(|clause| clause.evaluate(assignment)).reduce(|a, b| a && b).unwrap_or(true)
    }
}

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
                let (variable_ref, is_negative) = match literal {
                    Literal::Positive(variable_ref) => (variable_ref, false),
                    Literal::Negative(variable_ref) => (variable_ref, true),
                };
                let variable_name = &self.variables[variable_ref.0 as usize].name;
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
}

#[derive(Debug)]
enum Satisfiability {
    Satisfiable(Assignment),
    Unsatisfiable,
}

// TODO: Return satisfying (partial) assignment
fn dpll(formula: &Formula) -> Satisfiability {
    fn go(formula: &Formula, assignment: &Assignment) -> Satisfiability {
        if formula.clauses.is_empty() {
            return Satisfiability::Satisfiable(assignment.clone());
        }

        // Unit clause rule
        fn first_unit_clause_literal(formula: &Formula) -> Option<Literal> {
            for clause in &formula.clauses {
                if clause.literals.len() == 1 {
                    return Some(clause.literals[0]);
                }
            }

            None
        }
        if let Some(literal) = first_unit_clause_literal(formula) {
            let clauses = formula.clauses.iter().filter_map(|clause| {
                if clause.literals.contains(&literal) {
                    return None;
                }

                let literals = clause.literals.iter().copied().filter(|&l| l != -literal).collect::<Vec<_>>();
                if !literals.is_empty() {
                    Some(Clause {
                        literals,
                    })
                } else {
                    None
                }
            }).collect();
            let mut assignment = assignment.clone();
            let (variable_ref, value) = match literal {
                Literal::Positive(variable_ref) => (variable_ref, true),
                Literal::Negative(variable_ref) => (variable_ref, false),
            };
            assignment.values.insert(variable_ref, value);
            return go(&Formula {
                clauses,
            }, &assignment);
        }

        // Pure literal rule
        fn first_pure_literal(formula: &Formula) -> Option<Literal> {
            let mut literal_map = HashMap::new();
            for clause in &formula.clauses {
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
        if let Some(literal) = first_pure_literal(formula) {
            let clauses = formula.clauses.iter().filter(|clause| {
                !clause.literals.contains(&literal) && !clause.literals.contains(&-literal)
            }).cloned().collect();
            let mut assignment = assignment.clone();
            let (variable_ref, value) = match literal {
                Literal::Positive(variable_ref) => (variable_ref, true),
                Literal::Negative(variable_ref) => (variable_ref, false),
            };
            assignment.values.insert(variable_ref, value);
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
    let result = dpll(&instance.formula);
    println!("DPLL result: {:?}", result);
    if let Satisfiability::Satisfiable(assignment) = result {
        assert!(instance.formula.evaluate(&assignment));
    }
}
