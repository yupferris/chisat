use crate::ir::*;

use std::io;

pub fn serialize(formula: &Formula, mut w: impl io::Write) -> io::Result<()> {
    writeln!(w, "p cnf {} {}", formula.num_variables(), formula.num_clauses())?;

    for clause in &formula.clauses {
        for literal in &clause.literals {
            if !literal.is_positive {
                write!(w, "-")?;

            }
            write!(w, "{} ", literal.variable.index() + 1)?;
        }
        writeln!(w, "0")?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::dimacs_cnf::*;

    #[test]
    fn serialize_simple() -> io::Result<()> {
        let mut formula = Formula::new();
        formula.clause()
            .literal(Variable::from_index(0), true)
            .literal(Variable::from_index(1), false)
            .literal(Variable::from_index(2), true);
        formula.clause()
            .literal(Variable::from_index(1), false)
            .literal(Variable::from_index(0), false);
        formula.clause()
            .literal(Variable::from_index(2), false);

        let mut serialized = Vec::new();
        serialize(&formula, &mut serialized)?;

        let expected = br#"p cnf 3 3
1 -2 3 0
-2 -1 0
-3 0
"#;

        assert_eq!(expected, &serialized[..]);

        Ok(())
    }

    #[quickcheck]
    fn serialize_parse_round_trip(formula: Formula) -> io::Result<()> {
        let mut serialized = Vec::new();
        serialize(&formula, &mut serialized)?;

        let mut other = Formula::new();
        parse(&mut other, &serialized[..])?;

        let mut other_serialized = Vec::new();
        serialize(&other, &mut other_serialized)?;

        assert_eq!(serialized, other_serialized);

        Ok(())
    }
}
