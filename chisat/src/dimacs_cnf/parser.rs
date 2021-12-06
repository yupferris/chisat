use crate::ir::*;

mod transposing_peekable;

use transposing_peekable::*;

use std::io;

pub fn parse(formula: &mut Formula, r: impl io::Read) -> io::Result<()> {
    let mut p = r.bytes().transposing_peekable();

    accept_comments(&mut p)?;
    accept_whitespace(&mut p)?;
    let (num_variables, num_clauses) = expect_problem_line(&mut p)?;
    accept_whitespace(&mut p)?;

    // TODO: Validate num variables+clauses against allowed maximum

    let literal_to_variable = |literal: i32| -> io::Result<Variable> {
        let abs_literal = literal.abs() as u32;
        if abs_literal <= num_variables {
            Ok(Variable::from_index(abs_literal - 1))
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "Out-of-bounds literal value found: ({}, max {} variables specified)",
                    literal,
                    num_variables,
                ),
            ))
        }
    };
    let mut num_parsed_clauses = 0;
    while let Some(literal) = accept_i32(&mut p)? {
        num_parsed_clauses += 1;
        if num_parsed_clauses > num_clauses {
            break;
        }

        if literal == 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Expected clause, found terminal literal",
            ));
        }
        accept_whitespace(&mut p)?;

        let mut clause = formula.clause();
        clause.literal(literal_to_variable(literal)?, literal >= 0);

        loop {
            let literal = expect_i32(&mut p)?;
            accept_whitespace(&mut p)?;
            if literal == 0 {
                break;
            }

            clause.literal(literal_to_variable(literal)?, literal >= 0);
        }
    }

    if num_parsed_clauses != num_clauses {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "Number of parsed clauses doesn't match the number of expected clauses ({} and {}, respectively)",
                num_parsed_clauses,
                num_clauses,
            ),
        ));
    }

    Ok(())
}

fn accept_comments<I>(p: &mut TransposingPeekable<u8, I>) -> io::Result<()>
where
    I: Iterator<Item = io::Result<u8>>
{
    while accept_comment(p)? {
        // Do nothing
    }

    Ok(())
}

fn accept_comment<I>(p: &mut TransposingPeekable<u8, I>) -> io::Result<bool>
where
    I: Iterator<Item = io::Result<u8>>
{
    if let Some(_) = p.next_if_eq(&('c' as _))? {
        accept_all_until_next_line(p).map(|_| true)
    } else {
        Ok(false)
    }
}

fn accept_all_until_next_line<I>(p: &mut TransposingPeekable<u8, I>) -> io::Result<()>
where
    I: Iterator<Item = io::Result<u8>>
{
    while let Some(c) = p.next()? {
        if c == '\n' as _ {
            break;
        }
    }

    Ok(())
}

fn expect_problem_line<I>(p: &mut TransposingPeekable<u8, I>) -> io::Result<(u32, u32)>
where
    I: Iterator<Item = io::Result<u8>>
{
    expect_char(p, 'p')?;
    accept_whitespace(p)?;
    expect_str(p, "cnf")?;
    accept_whitespace(p)?;
    let num_variables = expect_u32(p)?;
    accept_whitespace(p)?;
    let num_clauses = expect_u32(p)?;

    Ok((num_variables, num_clauses))
}

fn expect_char<I>(p: &mut TransposingPeekable<u8, I>, c: char) -> io::Result<()>
where
    I: Iterator<Item = io::Result<u8>>
{
    match p.next()? {
        Some(next) if next == c as _ => {
            Ok(())
        }
        _ => Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("Expected char: '{}'", c),
        ))
    }
}

fn expect_str<I>(p: &mut TransposingPeekable<u8, I>, s: &str) -> io::Result<()>
where
    I: Iterator<Item = io::Result<u8>>
{
    for c in s.chars() {
        // TODO: Map/wrap error message?
        expect_char(p, c)?;
    }

    Ok(())
}

fn accept_whitespace<I>(p: &mut TransposingPeekable<u8, I>) -> io::Result<()>
where
    I: Iterator<Item = io::Result<u8>>
{
    while let Some(_) = p.next_if(|&b| (b as char).is_whitespace())? {
        // Do nothing
    }

    Ok(())
}

fn expect_i32<I>(p: &mut TransposingPeekable<u8, I>) -> io::Result<i32>
where
    I: Iterator<Item = io::Result<u8>>
{
    accept_i32(p)?.ok_or_else(|| io::Error::new(
        io::ErrorKind::InvalidData,
        "Expected signed 32-bit integer literal",
    ))
}

fn accept_i32<I>(p: &mut TransposingPeekable<u8, I>) -> io::Result<Option<i32>>
where
    I: Iterator<Item = io::Result<u8>>
{
    let minus = '-' as u8;
    let is_negative = p.next_if_eq(&minus)?.is_some();

    let mut ret: Option<i32> = None;
    let zero = '0' as u8;
    let nine = '9' as u8;
    while let Some(digit) = p.next_if(|&byte| byte >= zero && byte <= nine)? {
        let digit = (digit - zero) as i32;
        let digit = if is_negative { -digit } else { digit };
        ret = Some(if let Some(ret) = ret {
            match ret.checked_mul(10).and_then(|ret| ret.checked_add(digit)) {
                Some(ret) => ret,
                None => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "Signed integer literal does not fit in 32 bits",
                    ));
                }
            }
        } else {
            digit
        });
    }

    Ok(ret)
}

fn expect_u32<I>(p: &mut TransposingPeekable<u8, I>) -> io::Result<u32>
where
    I: Iterator<Item = io::Result<u8>>
{
    accept_u32(p)?.ok_or_else(|| io::Error::new(
        io::ErrorKind::InvalidData,
        "Expected unsigned 32-bit integer literal",
    ))
}

fn accept_u32<I>(p: &mut TransposingPeekable<u8, I>) -> io::Result<Option<u32>>
where
    I: Iterator<Item = io::Result<u8>>
{
    let mut ret: Option<u32> = None;
    let zero = '0' as u8;
    let nine = '9' as u8;
    while let Some(digit) = p.next_if(|&byte| byte >= zero && byte <= nine)? {
        let digit = (digit - zero) as u32;
        ret = Some(if let Some(ret) = ret {
            match ret.checked_mul(10).and_then(|ret| ret.checked_add(digit)) {
                Some(ret) => ret,
                None => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "Unsigned integer literal does not fit in 32 bits",
                    ));
                }
            }
        } else {
            digit
        });
    }

    Ok(ret)
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::dimacs_cnf::*;

    #[test]
    fn parse_simple_round_trip() -> io::Result<()> {
        let simple = br#"p cnf 3 2
1 2 -3 0
-2 3 0
"#;

        let mut formula = Formula::new();
        parse(&mut formula, &simple[..])?;

        let mut serialized = Vec::new();
        serialize(&formula, &mut serialized)?;

        assert_eq!(simple, &serialized[..]);

        Ok(())
    }

    #[quickcheck]
    fn accept_i32_any(x: i32) -> io::Result<()> {
        assert_eq!(accept_i32_str(&format!("{}", x))?, Some(x));

        Ok(())
    }

    #[test]
    fn accept_i32_basic() -> io::Result<()> {
        assert_eq!(accept_i32_str("")?, None);
        assert_eq!(accept_i32_str(" ")?, None);
        assert_eq!(accept_i32_str("a")?, None);

        assert_eq!(accept_i32_str("0")?, Some(0));
        assert_eq!(accept_i32_str("1")?, Some(1));
        assert_eq!(accept_i32_str("9")?, Some(9));
        assert_eq!(accept_i32_str("127")?, Some(127));
        assert_eq!(accept_i32_str("128")?, Some(128));
        assert_eq!(accept_i32_str("255")?, Some(255));
        assert_eq!(accept_i32_str("256")?, Some(256));
        assert_eq!(accept_i32_str("1337")?, Some(1337));

        assert_eq!(accept_i32_str("-0")?, Some(0));
        assert_eq!(accept_i32_str("-1")?, Some(-1));
        assert_eq!(accept_i32_str("-9")?, Some(-9));
        assert_eq!(accept_i32_str("-1337")?, Some(-1337));

        assert_eq!(accept_i32_str("1337 and some other stuff")?, Some(1337));
        assert_eq!(accept_i32_str("-1337 and some other stuff")?, Some(-1337));

        assert_eq!(accept_i32_str(&format!("{}", i32::MAX))?, Some(i32::MAX));
        assert_eq!(accept_i32_str(&format!("{}", i32::MIN))?, Some(i32::MIN));

        assert_eq!(
            accept_i32_str(&format!("{}", i32::MAX as i64 + 1)).unwrap_err().to_string(),
            "Signed integer literal does not fit in 32 bits",
        );
        assert_eq!(
            accept_i32_str(&format!("{}", i32::MIN as i64 - 1)).unwrap_err().to_string(),
            "Signed integer literal does not fit in 32 bits",
        );

        Ok(())
    }

    fn accept_i32_str(s: &str) -> io::Result<Option<i32>> {
        let mut p = s.bytes().map(|b| Ok(b)).transposing_peekable();
        accept_i32(&mut p)
    }

    #[quickcheck]
    fn accept_u32_any(x: u32) -> io::Result<()> {
        assert_eq!(accept_u32_str(&format!("{}", x))?, Some(x));

        Ok(())
    }

    #[test]
    fn accept_u32_basic() -> io::Result<()> {
        assert_eq!(accept_u32_str("")?, None);
        assert_eq!(accept_u32_str(" ")?, None);
        assert_eq!(accept_u32_str("a")?, None);

        assert_eq!(accept_u32_str("0")?, Some(0));
        assert_eq!(accept_u32_str("1")?, Some(1));
        assert_eq!(accept_u32_str("9")?, Some(9));
        assert_eq!(accept_u32_str("127")?, Some(127));
        assert_eq!(accept_u32_str("128")?, Some(128));
        assert_eq!(accept_u32_str("255")?, Some(255));
        assert_eq!(accept_u32_str("256")?, Some(256));
        assert_eq!(accept_u32_str("1337")?, Some(1337));

        assert_eq!(accept_u32_str("1337 and some other stuff")?, Some(1337));

        assert_eq!(accept_u32_str(&format!("{}", u32::MAX))?, Some(u32::MAX));
        assert_eq!(accept_u32_str(&format!("{}", u32::MIN))?, Some(u32::MIN));

        assert_eq!(
            accept_u32_str(&format!("{}", u32::MAX as i64 + 1)).unwrap_err().to_string(),
            "Unsigned integer literal does not fit in 32 bits",
        );

        Ok(())
    }

    fn accept_u32_str(s: &str) -> io::Result<Option<u32>> {
        let mut p = s.bytes().map(|b| Ok(b)).transposing_peekable();
        accept_u32(&mut p)
    }
}
