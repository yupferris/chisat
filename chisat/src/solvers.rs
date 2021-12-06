use crate::ir::*;

pub fn backtracking(formula: &Formula) -> (Option<Assignment>, u32) {
    fn go(formula: &Formula, assignment: Assignment, num_search_steps: &mut u32) -> Option<Assignment> {
        if formula.evaluate(&assignment) {
            return Some(assignment);
        }
        if let Some(variable) = formula.first_unassigned_variable(&assignment) {
            for value in [false, true] {
                *num_search_steps += 1;
                let result = go(
                    formula,
                    assignment.assign(variable, value),
                    num_search_steps,
                );
                if result.is_some() {
                    return result;
                }
            }
        }
        None
    }
    let mut num_search_steps = 0;
    (go(formula, Assignment::empty(), &mut num_search_steps), num_search_steps)
}

pub fn dpll(formula: &Formula) -> (Option<Assignment>, u32) {
    fn go(formula: &Formula, assignment: Assignment, num_search_steps: &mut u32) -> Option<Assignment> {
        if formula.clauses.is_empty() {
            return Some(assignment);
        }

        if formula.clauses.iter().any(|clause| clause.is_empty()) {
            return None;
        }

        // Unit clause rule
        if let Some(literal) = formula.first_unit_clause_literal() {
            return go(
                &formula.assign(literal.variable, literal.is_positive),
                assignment.assign(literal.variable, literal.is_positive),
                num_search_steps,
            );
        }

        // Pure literal rule
        if let Some(literal) = formula.first_pure_literal() {
            return go(
                &formula.assign(literal.variable, literal.is_positive),
                assignment.assign(literal.variable, literal.is_positive),
                num_search_steps,
            );
        }

        // Splitting rule
        if let Some(variable) = formula.first_unassigned_variable(&assignment) {
            for value in [false, true] {
                *num_search_steps += 1;
                let result = go(
                    &formula.assign(variable, value),
                    assignment.assign(variable, value),
                    num_search_steps,
                );
                if result.is_some() {
                    return result;
                }
            }
        }

        None
    }
    let mut num_search_steps = 0;
    (go(formula, Assignment::empty(), &mut num_search_steps), num_search_steps)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[quickcheck]
    fn backtracking_satisfying_assignments_are_satisfying(formula: Formula) {
        if let Some(assignment) = backtracking(&formula).0 {
            println!("Satisfying assignment: {:?}", assignment);
            assert!(formula.evaluate(&assignment));
        }
    }

    #[quickcheck]
    fn dpll_satisfying_assignments_are_satisfying(formula: Formula) {
        if let Some(assignment) = dpll(&formula).0 {
            println!("Satisfying assignment: {:?}", assignment);
            assert!(formula.evaluate(&assignment));
        }
    }

    #[quickcheck]
    fn backtracking_and_dpll_reach_the_same_conclusion(formula: Formula) {
        let backtracking_result = backtracking(&formula);
        println!("backtracking result: {:?}", backtracking_result);
        let dpll_result = dpll(&formula);
        println!("dpll result: {:?}", dpll_result);
        let ret = backtracking_result.0.is_some() == dpll_result.0.is_some();
        println!();
        assert!(ret);
    }

    #[quickcheck]
    fn dpll_uses_the_same_or_fewer_search_steps_than_backtracking(formula: Formula) {
        let backtracking_result = backtracking(&formula);
        println!("backtracking result: {:?}", backtracking_result);
        let dpll_result = dpll(&formula);
        println!("dpll result: {:?}", dpll_result);
        assert!(dpll_result.1 <= backtracking_result.1);
    }
}
