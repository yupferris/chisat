#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

#[cfg(test)]
mod tests {
    extern crate quickcheck;

    use chisat::*;
    use chisat::solvers::*;
    use variant_count::*;

    use std::collections::HashMap;

    struct Variable {
        name: String,
    }

    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    struct VariableRef(u32);

    #[derive(Clone)]
    enum Constraint {
        EqualityConst(VariableRef, bool),
        ExactlyOne(Vec<VariableRef>),
    }

    #[derive(Clone, Copy)]
    enum TransitionValue {
        Variable(VariableRef),
    }

    #[derive(Clone, Copy)]
    struct TransitionConstraint {
        variable: VariableRef,
        value: TransitionValue,
    }

    #[derive(Clone)]
    enum Property {
        Constraint(Constraint),
    }

    // TODO: Rename?
    struct System {
        variables: Vec<Variable>,

        init_constraints: Vec<Constraint>,
        transition_constraints: Vec<TransitionConstraint>,
    }

    impl System {
        fn new() -> System {
            System {
                variables: Vec::new(),

                init_constraints: Vec::new(),
                transition_constraints: Vec::new(),
            }
        }

        fn variable(&mut self, name: impl Into<String>) -> VariableRef {
            let name = name.into();
            assert!(self.variables.iter().all(|v| v.name != name));
            let ret = VariableRef(self.variables.len() as _);
            self.variables.push(Variable {
                name
            });
            ret
        }

        fn init_constraint(&mut self, c: Constraint) {
            self.init_constraints.push(c);
        }

        fn transition_constraint(&mut self, variable: VariableRef, value: TransitionValue) {
            assert!(self.transition_constraints.iter().all(|c| c.variable != variable));
            self.transition_constraints.push(TransitionConstraint {
                variable,
                value,
            });
        }
    }

    #[derive(Clone, Debug, VariantCount)]
    enum BooleanExpression {
        Conjuction(Box<BooleanExpression>, Box<BooleanExpression>),
        Disjuction(Box<BooleanExpression>, Box<BooleanExpression>),
        Equality(Box<BooleanExpression>, Box<BooleanExpression>),
        Negation(Box<BooleanExpression>),
        Variable(VariableRef),
    }

    #[derive(Clone)]
    struct Assignment {
        pub values: HashMap<VariableRef, bool>,
    }

    impl Assignment {
        fn assign(&self, variable: VariableRef, value: bool) -> Assignment {
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

    impl BooleanExpression {
        fn evaluate(&self, assignment: &Assignment) -> bool {
            match self {
                BooleanExpression::Conjuction(lhs, rhs) => lhs.evaluate(assignment) & rhs.evaluate(assignment),
                BooleanExpression::Disjuction(lhs, rhs) => lhs.evaluate(assignment) | rhs.evaluate(assignment),
                BooleanExpression::Equality(lhs, rhs) => lhs.evaluate(assignment) == rhs.evaluate(assignment),
                BooleanExpression::Negation(expression) => !expression.evaluate(assignment),
                BooleanExpression::Variable(variable) => assignment.values.get(&variable).cloned().unwrap_or(false),
            }
        }

        fn first_unassigned_variable(&self, assignment: &Assignment) -> Option<VariableRef> {
            match self {
                BooleanExpression::Conjuction(lhs, rhs) =>
                    lhs.first_unassigned_variable(assignment).or_else(|| rhs.first_unassigned_variable(assignment)),
                BooleanExpression::Disjuction(lhs, rhs) =>
                    lhs.first_unassigned_variable(assignment).or_else(|| rhs.first_unassigned_variable(assignment)),
                BooleanExpression::Equality(lhs, rhs) =>
                    lhs.first_unassigned_variable(assignment).or_else(|| rhs.first_unassigned_variable(assignment)),
                BooleanExpression::Negation(expression) => expression.first_unassigned_variable(assignment),
                &BooleanExpression::Variable(variable) => if !assignment.values.contains_key(&variable) {
                    Some(variable)
                } else {
                    None
                }
            }
        }

        fn is_satisfiable(&self) -> bool {
            fn go(expression: &BooleanExpression, assignment: Assignment) -> bool {
                if expression.evaluate(&assignment) {
                    return true;
                }
                if let Some(variable) = expression.first_unassigned_variable(&assignment) {
                    for value in [false, true] {
                        if go(
                            expression,
                            assignment.assign(variable, value),
                        ) {
                            return true;
                        }
                    }
                }
                return false;
            }

            return go(self, Assignment::empty())
        }
    }

    fn tseitin_transformation(expression: &BooleanExpression, variables: &mut Vec<Variable>) -> Formula {
        let mut ret = Formula::new();
        fn go(
            expression: &BooleanExpression,
            is_positive: bool,
            formula: &mut Formula,
            variables: &mut Vec<Variable>,
        ) -> chisat::Variable {
            match expression {
                BooleanExpression::Conjuction(lhs, rhs) => {
                    let lhs = go(lhs, true, formula, variables);
                    let rhs = go(rhs, true, formula, variables);
                    let temp_index = variables.len() as u32;
                    variables.push(Variable {
                        name: format!("_t{}", temp_index),
                    });
                    let temp = chisat::Variable::from_index(temp_index);
                    formula.clause()
                        .literal(lhs, false)
                        .literal(rhs, false)
                        .literal(temp, is_positive);
                    formula.clause()
                        .literal(lhs, true)
                        .literal(temp, !is_positive);
                    formula.clause()
                        .literal(rhs, true)
                        .literal(temp, !is_positive);
                    temp
                }
                BooleanExpression::Disjuction(lhs, rhs) => {
                    let lhs = go(lhs, true, formula, variables);
                    let rhs = go(rhs, true, formula, variables);
                    let temp_index = variables.len() as u32;
                    variables.push(Variable {
                        name: format!("_t{}", temp_index),
                    });
                    let temp = chisat::Variable::from_index(temp_index);
                    formula.clause()
                        .literal(lhs, true)
                        .literal(rhs, true)
                        .literal(temp, !is_positive);
                    formula.clause()
                        .literal(lhs, false)
                        .literal(temp, is_positive);
                    formula.clause()
                        .literal(rhs, false)
                        .literal(temp, is_positive);
                    temp
                }
                BooleanExpression::Equality(lhs, rhs) => {
                    let lhs = go(lhs, true, formula, variables);
                    let rhs = go(rhs, true, formula, variables);
                    let temp_index = variables.len() as u32;
                    variables.push(Variable {
                        name: format!("_t{}", temp_index),
                    });
                    let temp = chisat::Variable::from_index(temp_index);
                    formula.clause()
                        .literal(lhs, false)
                        .literal(rhs, false)
                        .literal(temp, is_positive);
                    formula.clause()
                        .literal(lhs, true)
                        .literal(rhs, true)
                        .literal(temp, is_positive);
                    formula.clause()
                        .literal(lhs, true)
                        .literal(rhs, false)
                        .literal(temp, !is_positive);
                    formula.clause()
                        .literal(lhs, false)
                        .literal(rhs, true)
                        .literal(temp, !is_positive);
                    temp
                }
                BooleanExpression::Negation(expression) => {
                    go(expression, !is_positive, formula, variables)
                }
                BooleanExpression::Variable(variable) => {
                    let variable = chisat::Variable::from_index(variable.0);
                    if is_positive {
                        variable
                    } else {
                        let temp_index = variables.len() as u32;
                        variables.push(Variable {
                            name: format!("_t{}", temp_index),
                        });
                        let temp = chisat::Variable::from_index(temp_index);
                        formula.clause()
                            .literal(variable, false)
                            .literal(temp, false);
                        formula.clause()
                            .literal(variable, true)
                            .literal(temp, true);
                        temp
                    }
                }
            }
        }
        let variable = go(expression, true, &mut ret, variables);
        ret.clause().literal(variable, true);
        ret
    }

    const ARBITRARY_NUM_VARIABLES: u32 = 8;

    impl quickcheck::Arbitrary for BooleanExpression {
        fn arbitrary(g: &mut quickcheck::Gen) -> Self {
            fn go(g: &mut quickcheck::Gen, depth: u32) -> BooleanExpression {
                // TODO: Use size?
                let max_depth = 4;
                if depth < max_depth {
                    match usize::arbitrary(g) % BooleanExpression::VARIANT_COUNT {
                        0 => BooleanExpression::Conjuction(Box::new(go(g, depth + 1)), Box::new(go(g, depth + 1))),
                        1 => BooleanExpression::Disjuction(Box::new(go(g, depth + 1)), Box::new(go(g, depth + 1))),
                        2 => BooleanExpression::Equality(Box::new(go(g, depth + 1)), Box::new(go(g, depth + 1))),
                        3 => BooleanExpression::Negation(Box::new(go(g, depth + 1))),
                        4 => BooleanExpression::Variable(VariableRef(u32::arbitrary(g) % ARBITRARY_NUM_VARIABLES)),
                        _ => unreachable!()
                    }
                } else {
                    BooleanExpression::Variable(VariableRef(u32::arbitrary(g) % ARBITRARY_NUM_VARIABLES))
                }
            }
            go(g, 0)
        }
    }

    #[quickcheck]
    fn tseitin_transformation_is_equisatisfiable(expression: BooleanExpression) {
        let mut variables = (0..ARBITRARY_NUM_VARIABLES).map(|i| Variable {
            name: format!("v{}", i),
        }).collect();
        let formula = tseitin_transformation(&expression, &mut variables);
        println!("formula: {:?}", formula);

        let result = dpll(&formula);
        println!("result: {:?}", result);

        if let Some(result) = result.0 {
            let assignment = Assignment {
                values: result.values.iter().map(|(variable, &value)| (VariableRef(variable.index()), value)).collect(),
            };
            assert!(expression.evaluate(&assignment));
        } else {
            assert!(!expression.is_satisfiable());
        }
    }

    #[test]
    fn rename_me_pls() {
        let mut system = System::new();

        let a = system.variable("a");
        let b = system.variable("b");
        let c = system.variable("c");

        system.init_constraint(Constraint::EqualityConst(a, true));
        system.init_constraint(Constraint::EqualityConst(b, false));
        system.init_constraint(Constraint::EqualityConst(c, false));

        system.transition_constraint(a, TransitionValue::Variable(c));
        system.transition_constraint(b, TransitionValue::Variable(a));
        system.transition_constraint(c, TransitionValue::Variable(b));

        println!("system:");
        println!("  variables:");
        for variable in &system.variables {
            println!("    {}", variable.name);
        }
        println!("  init constraints:");
        for constraint in &system.init_constraints {
            match constraint {
                Constraint::EqualityConst(variable, value) => {
                    println!("    {} = {}", system.variables[variable.0 as usize].name, value);
                }
                Constraint::ExactlyOne(ref variables) => {
                    print!("    EO(");
                    for (i, &variable) in variables.iter().enumerate() {
                        if i > 0 {
                            print!(", ");
                        }
                        print!("{}", system.variables[variable.0 as usize].name);
                    }
                    println!(")");
                }
            }
        }
        println!("  transition constraints:");
        for constraint in &system.transition_constraints {
            print!("    {}' = ", system.variables[constraint.variable.0 as usize].name);
            match constraint.value {
                TransitionValue::Variable(variable) => {
                    println!("{}", system.variables[variable.0 as usize].name);
                }
            }
        }

        let properties = vec![
            Property::Constraint(Constraint::ExactlyOne(vec![a, b, c])),
            // Bogus property to see that induction fails correctly
            //Property::Constraint(Constraint::EqualityConst(c, false)),
        ];
        println!("  properties:");
        for property in &properties {
            match property {
                Property::Constraint(constraint) => {
                    match constraint {
                        Constraint::EqualityConst(variable, value) => {
                            println!("    {} = {}", system.variables[variable.0 as usize].name, value);
                        }
                        Constraint::ExactlyOne(ref variables) => {
                            print!("    EO(");
                            for (i, &variable) in variables.iter().enumerate() {
                                if i > 0 {
                                    print!(", ");
                                }
                                print!("{}", system.variables[variable.0 as usize].name);
                            }
                            println!(")");
                        }
                    }
                }
            }
        }

        println!("Base case");
        let mut variables = system.variables.iter().map(|v| Variable {
            name: v.name.clone(),
        }).collect();
        let mut expression: Option<BooleanExpression> = None;
        let mut conjoin = |e: BooleanExpression| {
            expression = Some(if let Some(expression) = expression.as_ref() {
                // TODO: This clone sucks
                BooleanExpression::Conjuction(Box::new(expression.clone()), Box::new(e))
            } else {
                e
            });
        };
        for constraint in &system.init_constraints {
            conjoin(match constraint {
                &Constraint::EqualityConst(variable, value) => {
                    if value {
                        BooleanExpression::Variable(variable)
                    } else {
                        BooleanExpression::Negation(Box::new(BooleanExpression::Variable(variable)))
                    }
                }
                &Constraint::ExactlyOne(ref input_variables) => {
                    encode_exactly_one_constraint(input_variables)
                }
            })
        }
        for property in &properties {
            conjoin(BooleanExpression::Negation(Box::new(match property {
                Property::Constraint(constraint) => {
                    match constraint {
                        &Constraint::EqualityConst(variable, value) => {
                            if value {
                                BooleanExpression::Variable(variable)
                            } else {
                                BooleanExpression::Negation(Box::new(BooleanExpression::Variable(variable)))
                            }
                        }
                        &Constraint::ExactlyOne(ref input_variables) => {
                            encode_exactly_one_constraint(input_variables)
                        }
                    }
                }
            })))
        }
        let formula = tseitin_transformation(&expression.unwrap(), &mut variables);
        //println!("  formula: {:?}", formula);

        let result = dpll(&formula);
        println!("  result: {:?}", result);
        if let Some(assignment) = result.0 {
            panic!("Base case check failed");
            // TODO
        }

        println!("Base case check successful");

        println!("Induction");
        let mut variables = system.variables.iter().map(|v| Variable {
            name: v.name.clone(),
        }).chain(system.variables.iter().map(|v| Variable {
            name: format!("{}'", v.name),
        })).collect();
        let mut expression: Option<BooleanExpression> = None;
        let mut conjoin = |e: BooleanExpression| {
            expression = Some(if let Some(expression) = expression.as_ref() {
                // TODO: This clone sucks
                BooleanExpression::Conjuction(Box::new(expression.clone()), Box::new(e))
            } else {
                e
            });
        };
        let primed = |variable: VariableRef| {
            VariableRef(variable.0 + system.variables.len() as u32)
        };
        for &constraint in &system.transition_constraints {
            let x = primed(constraint.variable);
            let y = match constraint.value {
                TransitionValue::Variable(variable) => variable,
            };
            conjoin(BooleanExpression::Equality(
                Box::new(BooleanExpression::Variable(x)),
                Box::new(BooleanExpression::Variable(y)),
            ));
        }
        for property in &properties {
            match property {
                Property::Constraint(constraint) => {
                    match constraint {
                        &Constraint::EqualityConst(variable, value) => {
                            conjoin(if value {
                                BooleanExpression::Variable(variable)
                            } else {
                                BooleanExpression::Negation(Box::new(BooleanExpression::Variable(variable)))
                            });
                            let primed_variable = primed(variable);
                            conjoin(BooleanExpression::Negation(Box::new(
                                if value {
                                    BooleanExpression::Variable(primed_variable)
                                } else {
                                    BooleanExpression::Negation(Box::new(BooleanExpression::Variable(primed_variable)))
                                }
                            )));
                        }
                        &Constraint::ExactlyOne(ref input_variables) => {
                            conjoin(encode_exactly_one_constraint(input_variables));
                            let primed_input_variables = input_variables.iter().cloned().map(primed).collect::<Vec<_>>();
                            conjoin(BooleanExpression::Negation(Box::new(
                                encode_exactly_one_constraint(&primed_input_variables)
                            )));
                        }
                    }
                }
            }
        }
        let formula = tseitin_transformation(&expression.unwrap(), &mut variables);
        //println!("  formula: {:?}", formula);

        let result = dpll(&formula);
        println!("  result: {:?}", result);
        if let Some(assignment) = result.0 {
            println!("Induction check failed!");

            println!("From state:");
            for &constraint in &system.transition_constraints {
                println!(
                    "  {} = {}",
                    system.variables[constraint.variable.0 as usize].name,
                    assignment.values[&chisat::Variable::from_index(constraint.variable.0)],
                );
            }

            println!("To state:");
            for &constraint in &system.transition_constraints {
                println!(
                    "  {}' = {}",
                    system.variables[constraint.variable.0 as usize].name,
                    assignment.values[&chisat::Variable::from_index(primed(constraint.variable).0)],
                );
            }

            panic!("Induction check failed!");
        }

        println!("Induction check successful");
    }

    fn encode_exactly_one_constraint(input_variables: &[VariableRef]) -> BooleanExpression {
        BooleanExpression::Conjuction(
            Box::new(encode_at_least_one_constraint(input_variables)),
            Box::new(encode_at_most_one_constraint(input_variables)),
        )
    }

    fn encode_at_least_one_constraint(input_variables: &[VariableRef]) -> BooleanExpression {
        let mut expression: Option<BooleanExpression> = None;
        let mut disjoin = |e: BooleanExpression| {
            expression = Some(if let Some(expression) = expression.as_ref() {
                // TODO: This clone sucks
                BooleanExpression::Disjuction(Box::new(expression.clone()), Box::new(e))
            } else {
                e
            });
        };
        for &variable in input_variables {
            disjoin(BooleanExpression::Variable(variable));
        }
        expression.unwrap()
    }

    fn encode_at_most_one_constraint(input_variables: &[VariableRef]) -> BooleanExpression {
        let mut expression: Option<BooleanExpression> = None;
        let mut conjoin = |e: BooleanExpression| {
            expression = Some(if let Some(expression) = expression.as_ref() {
                // TODO: This clone sucks
                BooleanExpression::Conjuction(Box::new(expression.clone()), Box::new(e))
            } else {
                e
            });
        };
        for y_index in 0..input_variables.len() {
            let y = input_variables[y_index];
            for x_index in 0..y_index {
                let x = input_variables[x_index];
                conjoin(BooleanExpression::Negation(Box::new(
                    BooleanExpression::Conjuction(
                        Box::new(BooleanExpression::Variable(x)),
                        Box::new(BooleanExpression::Variable(y)),
                    ))
                ));
            }
        }
        expression.unwrap()
    }
}
