use crate::tseitin_transformation::*;

use typed_arena::Arena;

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::ops::{BitAnd, BitOr, Not};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Assignment {
    pub(crate) values: HashMap<String, bool>,
}

impl Assignment {
    pub fn assign(&self, name: String, value: bool) -> Assignment {
        let mut ret = self.clone();
        ret.values.insert(name, value);
        ret
    }

    pub fn empty() -> Assignment {
        Assignment {
            values: HashMap::new(),
        }
    }
}

pub struct Solver<'a> {
    arena: Arena<Expr<'a>>,

    state: RefCell<SolverState<'a>>,
}

impl<'a> Solver<'a> {
    pub fn new() -> Solver<'a> {
        Solver {
            arena: Arena::new(),

            state: RefCell::new(SolverState {
                assertions: None,

                true_: None,
                false_: None,

                variables: HashSet::new(),
            }),
        }
    }

    fn add(&'a self, assertion: &'a Expr<'a>) {
        // TODO: Ensure expr comes from this context
        let mut state = self.state.borrow_mut();
        // TODO: Feels like this could be expressed a bit better..?
        state.assertions = Some(
            state
                .assertions
                .map_or(assertion, |assertions| assertions & assertion),
        );
    }

    // TODO: Rename?
    pub fn const_(&'a self, value: bool) -> &'a Expr<'a> {
        let mut state = self.state.borrow_mut();
        // TODO: Rewrite this better
        let rename_me_pls = if value {
            &mut state.true_
        } else {
            &mut state.false_
        };
        if rename_me_pls.is_none() {
            *rename_me_pls = Some(self.arena.alloc(Expr {
                context: self,

                data: ExprData::Const { value },
            }));
        }
        rename_me_pls.unwrap()
    }

    fn solve(&'a self) -> Option<Assignment> {
        let true_ = self.const_(true);
        let state = self.state.borrow();
        let expr = state.assertions.unwrap_or(true_);
        let mut variables = HashMap::new();
        let formula = tseitin_transformation(expr, &mut variables);
        chisat::solvers::dpll(&formula).0.map(|result| {
            let mut ret = Assignment::empty();

            for variable in &state.variables {
                if let Some(id) = variables.get(variable) {
                    if let Some(value) = result.values.get(&chisat::Variable::from_index(*id)) {
                        ret.values.insert(variable.clone(), *value);
                    }
                }
            }

            ret
        })
    }

    pub fn variable(&'a self, name: impl Into<String>) -> &'a Expr<'a> {
        let name = name.into();
        // TODO: Ensure uniqueness for `name`
        self.state.borrow_mut().variables.insert(name.clone());
        self.arena.alloc(Expr {
            context: self,

            data: ExprData::Variable { name },
        })
    }
}

struct SolverState<'a> {
    assertions: Option<&'a Expr<'a>>,

    true_: Option<&'a Expr<'a>>,
    false_: Option<&'a Expr<'a>>,

    variables: HashSet<String>,
}

pub struct Expr<'a> {
    context: &'a Solver<'a>,

    pub(crate) data: ExprData<'a>,
}

impl<'a> Expr<'a> {
    pub fn eq(&'a self, rhs: &'a Self) -> &'a Self {
        // TODO: Ensure rhs comes from the same context as self
        self.context.arena.alloc(Expr {
            context: self.context,

            data: ExprData::Equality { lhs: self, rhs },
        })
    }
}

impl<'a> BitAnd for &'a Expr<'a> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        // TODO: Ensure rhs comes from the same context as self
        self.context.arena.alloc(Expr {
            context: self.context,

            data: ExprData::Conjunction { lhs: self, rhs },
        })
    }
}

impl<'a> BitOr for &'a Expr<'a> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        // TODO: Ensure rhs comes from the same context as self
        self.context.arena.alloc(Expr {
            context: self.context,

            data: ExprData::Disjunction { lhs: self, rhs },
        })
    }
}

impl<'a> Not for &'a Expr<'a> {
    type Output = Self;

    fn not(self) -> Self::Output {
        // TODO: Ensure rhs comes from the same context as self
        self.context.arena.alloc(Expr {
            context: self.context,

            data: ExprData::Negation { expr: self },
        })
    }
}

pub(crate) enum ExprData<'a> {
    Conjunction {
        lhs: &'a Expr<'a>,
        rhs: &'a Expr<'a>,
    },
    Const {
        value: bool,
    },
    Disjunction {
        lhs: &'a Expr<'a>,
        rhs: &'a Expr<'a>,
    },
    Equality {
        lhs: &'a Expr<'a>,
        rhs: &'a Expr<'a>,
    },
    Negation {
        expr: &'a Expr<'a>,
    },
    // TODO: Rename?
    // TODO: Use ID instead of string? Is this problematic?
    Variable {
        name: String,
    },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_boolean_var_true() {
        let s = Solver::new();

        let a = s.variable("a");

        s.add(a.eq(s.const_(true)));

        assert_eq!(
            s.solve(),
            Some(Assignment {
                values: vec![("a".into(), true),].into_iter().collect(),
            })
        );
    }

    #[test]
    fn single_boolean_var_false() {
        let s = Solver::new();

        let a = s.variable("a");

        s.add(a.eq(s.const_(false)));

        assert_eq!(
            s.solve(),
            Some(Assignment {
                values: vec![("a".into(), false),].into_iter().collect(),
            })
        );
    }

    #[test]
    fn simple_negation_true() {
        let s = Solver::new();

        let a = s.variable("a");

        s.add(a.eq(!s.const_(true)));

        assert_eq!(
            s.solve(),
            Some(Assignment {
                values: vec![("a".into(), false),].into_iter().collect(),
            })
        );
    }

    #[test]
    fn simple_negation_false() {
        let s = Solver::new();

        let a = s.variable("a");

        s.add(a.eq(!s.const_(false)));

        assert_eq!(
            s.solve(),
            Some(Assignment {
                values: vec![("a".into(), true),].into_iter().collect(),
            })
        );
    }

    #[test]
    fn simple_boolean_conjunction_true() {
        let s = Solver::new();

        let a = s.variable("a");
        let b = s.variable("b");
        let c = s.variable("c");

        s.add(a.eq(s.const_(true)));
        s.add(c.eq(s.const_(true)));
        s.add(c.eq(a & b));

        assert_eq!(
            s.solve(),
            Some(Assignment {
                values: vec![("a".into(), true), ("b".into(), true), ("c".into(), true),]
                    .into_iter()
                    .collect(),
            })
        );
    }

    #[test]
    fn simple_boolean_conjunction_false() {
        let s = Solver::new();

        let a = s.variable("a");
        let b = s.variable("b");
        let c = s.variable("c");

        s.add(a.eq(s.const_(true)));
        s.add(c.eq(s.const_(false)));
        s.add(c.eq(a & b));

        assert_eq!(
            s.solve(),
            Some(Assignment {
                values: vec![("a".into(), true), ("b".into(), false), ("c".into(), false),]
                    .into_iter()
                    .collect(),
            })
        );
    }

    #[test]
    fn simple_boolean_disjunction_true() {
        let s = Solver::new();

        let a = s.variable("a");
        let b = s.variable("b");
        let c = s.variable("c");

        s.add(a.eq(s.const_(false)));
        s.add(c.eq(s.const_(true)));
        s.add(c.eq(a | b));

        assert_eq!(
            s.solve(),
            Some(Assignment {
                values: vec![("a".into(), false), ("b".into(), true), ("c".into(), true),]
                    .into_iter()
                    .collect(),
            })
        );
    }

    #[test]
    fn simple_boolean_disjunction_false() {
        let s = Solver::new();

        let a = s.variable("a");
        let b = s.variable("b");
        let c = s.variable("c");

        s.add(a.eq(s.const_(false)));
        s.add(c.eq(s.const_(false)));
        s.add(c.eq(a | b));

        assert_eq!(
            s.solve(),
            Some(Assignment {
                values: vec![
                    ("a".into(), false),
                    ("b".into(), false),
                    ("c".into(), false),
                ]
                .into_iter()
                .collect(),
            })
        );
    }
}
