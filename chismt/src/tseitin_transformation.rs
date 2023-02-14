use crate::ir::*;

use variant_count::*;

use std::collections::HashMap;

pub fn tseitin_transformation<'a>(
    expr: &'a Expr<'a>,
    variables: &mut HashMap<String, u32>,
) -> chisat::Formula {
    let mut ret = chisat::Formula::new();
    fn go<'a>(
        expr: &'a Expr<'a>,
        is_positive: bool,
        formula: &mut chisat::Formula,
        variables: &mut HashMap<String, u32>,
    ) -> chisat::Variable {
        match expr.data {
            ExprData::Conjunction { lhs, rhs } => {
                let lhs = go(lhs, true, formula, variables);
                let rhs = go(rhs, true, formula, variables);
                let temp_index = variables.len() as u32;
                // TODO: Ensure name uniqueness
                variables.insert(format!("_t{}", temp_index), temp_index);
                let temp = chisat::Variable::from_index(temp_index);
                formula
                    .clause()
                    .literal(lhs, false)
                    .literal(rhs, false)
                    .literal(temp, is_positive);
                formula
                    .clause()
                    .literal(lhs, true)
                    .literal(temp, !is_positive);
                formula
                    .clause()
                    .literal(rhs, true)
                    .literal(temp, !is_positive);
                temp
            }
            ExprData::Const { value } => {
                // TODO: Consider reserving a couple variables for true/false and referring to those
                let temp_index = variables.len() as u32;
                // TODO: Ensure name uniqueness
                variables.insert(format!("_t{}", temp_index), temp_index);
                let temp = chisat::Variable::from_index(temp_index);
                formula.clause().literal(temp, value ^ !is_positive);
                temp
            }
            ExprData::Disjunction { lhs, rhs } => {
                let lhs = go(lhs, true, formula, variables);
                let rhs = go(rhs, true, formula, variables);
                let temp_index = variables.len() as u32;
                // TODO: Ensure name uniqueness
                variables.insert(format!("_t{}", temp_index), temp_index);
                let temp = chisat::Variable::from_index(temp_index);
                formula
                    .clause()
                    .literal(lhs, true)
                    .literal(rhs, true)
                    .literal(temp, !is_positive);
                formula
                    .clause()
                    .literal(lhs, false)
                    .literal(temp, is_positive);
                formula
                    .clause()
                    .literal(rhs, false)
                    .literal(temp, is_positive);
                temp
            }
            ExprData::Equality { lhs, rhs } => {
                let lhs = go(lhs, true, formula, variables);
                let rhs = go(rhs, true, formula, variables);
                let temp_index = variables.len() as u32;
                // TODO: Ensure name uniqueness
                variables.insert(format!("_t{}", temp_index), temp_index);
                let temp = chisat::Variable::from_index(temp_index);
                formula
                    .clause()
                    .literal(lhs, false)
                    .literal(rhs, false)
                    .literal(temp, is_positive);
                formula
                    .clause()
                    .literal(lhs, true)
                    .literal(rhs, true)
                    .literal(temp, is_positive);
                formula
                    .clause()
                    .literal(lhs, true)
                    .literal(rhs, false)
                    .literal(temp, !is_positive);
                formula
                    .clause()
                    .literal(lhs, false)
                    .literal(rhs, true)
                    .literal(temp, !is_positive);
                temp
            }
            ExprData::Negation { expr } => go(expr, !is_positive, formula, variables),
            ExprData::Variable { ref name } => {
                // TODO: Can we do this with less traversal/cloning?
                let variable =
                    chisat::Variable::from_index(if let Some(variable) = variables.get(name) {
                        *variable
                    } else {
                        let variable = variables.len() as u32;
                        variables.insert(name.clone(), variable);
                        variable
                    });
                if is_positive {
                    variable
                } else {
                    let temp_index = variables.len() as u32;
                    // TODO: Ensure name uniqueness
                    variables.insert(format!("_t{}", temp_index), temp_index);
                    let temp = chisat::Variable::from_index(temp_index);
                    formula
                        .clause()
                        .literal(variable, false)
                        .literal(temp, false);
                    formula.clause().literal(variable, true).literal(temp, true);
                    temp
                }
            }
        }
    }
    let variable = go(expr, true, &mut ret, variables);
    ret.clause().literal(variable, true);
    ret
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Debug, VariantCount)]
    enum BooleanExpression {
        Conjunction {
            lhs: Box<BooleanExpression>,
            rhs: Box<BooleanExpression>,
        },
        Const {
            value: bool,
        },
        Disjunction {
            lhs: Box<BooleanExpression>,
            rhs: Box<BooleanExpression>,
        },
        Equality {
            lhs: Box<BooleanExpression>,
            rhs: Box<BooleanExpression>,
        },
        Negation {
            expr: Box<BooleanExpression>,
        },
        Variable {
            name: String,
        },
    }

    impl BooleanExpression {
        fn expr<'a>(&self, s: &'a Solver<'a>) -> &'a Expr<'a> {
            match self {
                BooleanExpression::Conjunction { lhs, rhs } => lhs.expr(s) & rhs.expr(s),
                BooleanExpression::Const { value } => s.const_(*value),
                BooleanExpression::Disjunction { lhs, rhs } => lhs.expr(s) | rhs.expr(s),
                BooleanExpression::Equality { lhs, rhs } => lhs.expr(s).eq(rhs.expr(s)),
                BooleanExpression::Negation { expr } => !expr.expr(s),
                BooleanExpression::Variable { name } => s.variable(name.clone()),
            }
        }

        fn evaluate(&self, assignment: &Assignment) -> bool {
            match self {
                BooleanExpression::Conjunction { lhs, rhs } => {
                    lhs.evaluate(assignment) & rhs.evaluate(assignment)
                }
                BooleanExpression::Const { value } => *value,
                BooleanExpression::Disjunction { lhs, rhs } => {
                    lhs.evaluate(assignment) | rhs.evaluate(assignment)
                }
                BooleanExpression::Equality { lhs, rhs } => {
                    lhs.evaluate(assignment) == rhs.evaluate(assignment)
                }
                BooleanExpression::Negation { expr } => !expr.evaluate(assignment),
                BooleanExpression::Variable { name } => {
                    assignment.values.get(name).cloned().unwrap_or(false)
                }
            }
        }

        fn first_unassigned_variable(&self, assignment: &Assignment) -> Option<String> {
            match self {
                BooleanExpression::Conjunction { lhs, rhs } => lhs
                    .first_unassigned_variable(assignment)
                    .or_else(|| rhs.first_unassigned_variable(assignment)),
                BooleanExpression::Const { .. } => None,
                BooleanExpression::Disjunction { lhs, rhs } => lhs
                    .first_unassigned_variable(assignment)
                    .or_else(|| rhs.first_unassigned_variable(assignment)),
                BooleanExpression::Equality { lhs, rhs } => lhs
                    .first_unassigned_variable(assignment)
                    .or_else(|| rhs.first_unassigned_variable(assignment)),
                BooleanExpression::Negation { expr } => expr.first_unassigned_variable(assignment),
                BooleanExpression::Variable { name } => {
                    if !assignment.values.contains_key(name) {
                        Some(name.clone())
                    } else {
                        None
                    }
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
                        if go(expression, assignment.assign(variable.clone(), value)) {
                            return true;
                        }
                    }
                }
                return false;
            }

            return go(self, Assignment::empty());
        }
    }

    const ARBITRARY_NUM_VARIABLES: u32 = 8;

    impl quickcheck::Arbitrary for BooleanExpression {
        fn arbitrary(g: &mut quickcheck::Gen) -> Self {
            fn go(g: &mut quickcheck::Gen, depth: u32) -> BooleanExpression {
                // TODO: Use size?
                let max_depth = 4;
                if depth < max_depth {
                    match usize::arbitrary(g) % BooleanExpression::VARIANT_COUNT {
                        0 => BooleanExpression::Conjunction {
                            lhs: Box::new(go(g, depth + 1)),
                            rhs: Box::new(go(g, depth + 1)),
                        },
                        1 => BooleanExpression::Const {
                            value: bool::arbitrary(g),
                        },
                        2 => BooleanExpression::Disjunction {
                            lhs: Box::new(go(g, depth + 1)),
                            rhs: Box::new(go(g, depth + 1)),
                        },
                        3 => BooleanExpression::Equality {
                            lhs: Box::new(go(g, depth + 1)),
                            rhs: Box::new(go(g, depth + 1)),
                        },
                        4 => BooleanExpression::Negation {
                            expr: Box::new(go(g, depth + 1)),
                        },
                        5 => BooleanExpression::Variable {
                            name: format!("v{}", u32::arbitrary(g) % ARBITRARY_NUM_VARIABLES),
                        },
                        _ => unreachable!(),
                    }
                } else {
                    match usize::arbitrary(g) % 2 {
                        0 => BooleanExpression::Const {
                            value: bool::arbitrary(g),
                        },
                        1 => BooleanExpression::Variable {
                            name: format!("v{}", u32::arbitrary(g) % ARBITRARY_NUM_VARIABLES),
                        },
                        _ => unreachable!(),
                    }
                }
            }
            go(g, 0)
        }
    }

    #[quickcheck]
    fn tseitin_transformation_is_equisatisfiable(expression: BooleanExpression) {
        // TODO: Is there a lower-level context object that perhaps a Solver owns that we can use directly here instead?
        let s = Solver::new();
        let expr = expression.expr(&s);
        let mut variables = HashMap::new();
        let formula = tseitin_transformation(expr, &mut variables);
        println!("formula: {:?}", formula);

        let result = chisat::solvers::dpll(&formula);
        println!("result: {:?}", result);

        if let Some(result) = result.0 {
            let mut assignment = Assignment::empty();

            for (name, id) in &variables {
                if let Some(value) = result.values.get(&chisat::Variable::from_index(*id)) {
                    assignment.values.insert(name.clone(), *value);
                }
            }

            assert!(expression.evaluate(&assignment));
        } else {
            assert!(!expression.is_satisfiable());
        }
    }
}
