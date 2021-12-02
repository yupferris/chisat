use crate::ir::*;

pub fn backtracking(context: &Context) -> (Option<Assignment>, u32) {
    fn go(context: &Context, assignment: Assignment, num_search_steps: &mut u32) -> Option<Assignment> {
        if context.evaluate(&assignment) {
            return Some(assignment);
        }
        if let Some(variable) = context.first_unassigned_variable(&assignment) {
            for value in [false, true] {
                *num_search_steps += 1;
                let result = go(
                    context,
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
    (go(context, Assignment::empty(), &mut num_search_steps), num_search_steps)
}

pub fn dpll(context: &Context) -> (Option<Assignment>, u32) {
    fn go(context: &Context, assignment: Assignment, num_search_steps: &mut u32) -> Option<Assignment> {
        if context.clauses.is_empty() {
            return Some(assignment);
        }

        if context.clauses.iter().any(|clause| clause.is_empty()) {
            return None;
        }

        // Unit clause rule
        if let Some(literal) = context.first_unit_clause_literal() {
            return go(
                &context.assign(literal.variable, literal.is_positive),
                assignment.assign(literal.variable, literal.is_positive),
                num_search_steps,
            );
        }

        // Pure literal rule
        if let Some(literal) = context.first_pure_literal() {
            return go(
                &context.assign(literal.variable, literal.is_positive),
                assignment.assign(literal.variable, literal.is_positive),
                num_search_steps,
            );
        }

        // Splitting rule
        if let Some(variable) = context.first_unassigned_variable(&assignment) {
            for value in [false, true] {
                *num_search_steps += 1;
                let result = go(
                    &context.assign(variable, value),
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
    (go(context, Assignment::empty(), &mut num_search_steps), num_search_steps)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[quickcheck]
    fn backtracking_satisfying_assignments_are_satisfying(context: Context) -> bool {
        match backtracking(&context).0 {
            Some(assignment) => {
                println!("Satisfying assignment: {:?}", assignment);
                context.evaluate(&assignment)
            }
            _ => true,
        }
    }

    #[quickcheck]
    fn dpll_satisfying_assignments_are_satisfying(context: Context) -> bool {
        match dpll(&context).0 {
            Some(assignment) => {
                println!("Satisfying assignment: {:?}", assignment);
                context.evaluate(&assignment)
            }
            _ => true,
        }
    }

    #[quickcheck]
    fn backtracking_and_dpll_reach_the_same_conclusion(context: Context) -> bool {
        let backtracking_result = backtracking(&context);
        println!("backtracking result: {:?}", backtracking_result);
        let dpll_result = dpll(&context);
        println!("dpll result: {:?}", dpll_result);
        let ret = backtracking_result.0.is_some() == dpll_result.0.is_some();
        println!();
        ret
    }

    #[quickcheck]
    fn dpll_uses_the_same_or_fewer_search_steps_than_backtracking(context: Context) -> bool {
        let backtracking_result = backtracking(&context);
        println!("backtracking result: {:?}", backtracking_result);
        let dpll_result = dpll(&context);
        println!("dpll result: {:?}", dpll_result);
        dpll_result.1 <= backtracking_result.1
    }
}
