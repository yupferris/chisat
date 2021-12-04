use crate::ir::*;

use std::io;
use std::iter::Iterator;

// TODO: Rename?
struct TransposingPeekable<Item, I>
where
    I: Iterator<Item = io::Result<Item>>
{
    iter: I,
    peeked: Option<Option<Item>>,
}

impl<Item, I> TransposingPeekable<Item, I>
where
    I: Iterator<Item = io::Result<Item>>
{
    fn new(iter: I) -> TransposingPeekable<Item, I> {
        TransposingPeekable {
            iter,
            peeked: None,
        }
    }

    fn next(&mut self) -> io::Result<Option<Item>> {
        match self.peeked.take() {
            Some(peeked) => Ok(peeked),
            None => self.iter.next().transpose(),
        }
    }

    fn next_if(&mut self, func: impl FnOnce(&Item) -> bool) -> io::Result<Option<Item>> {
        Ok(match self.next()? {
            Some(peeked) if func(&peeked) => Some(peeked),
            other => {
                // Since we called `self.next()`, we consumed `self.peeked`
                assert!(self.peeked.is_none());
                self.peeked = Some(other);
                None
            }
        })
    }

    fn next_if_eq<T>(&mut self, expected: &T) -> io::Result<Option<Item>>
    where
        Item: PartialEq<T>,
    {
        self.next_if(|next| next == expected)
    }
}

// TODO: Write (more!) tests
pub fn parse(formula: &mut Formula, r: impl io::Read) -> io::Result<()> {
    // TODO: Consider IteratorExt with `err_forwarding_peekable` fn or something
    let mut p = TransposingPeekable::new(r.bytes());

    skip_comments(&mut p)?;
    skip_whitespace(&mut p)?;
    let (num_variables, num_clauses) = expect_problem_line(&mut p)?;
    skip_whitespace(&mut p)?;

    // TODO: Validate num variables+clauses against allowed maximum

    // TODO: Validate num_variables while parsing clauses
    let mut num_parsed_clauses = 0;
    while let Some(first_literal) = accept_i32(&mut p)? {
        if first_literal == 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Expected clause, found terminal literal",
            ));
        }
        skip_whitespace(&mut p)?;

        let mut clause = formula.clause();
        clause.literal(Variable::from_index(first_literal.abs() as u32 - 1), first_literal >= 0);

        loop {
            let literal = expect_i32(&mut p)?;
            skip_whitespace(&mut p)?;
            if literal == 0 {
                break;
            }

            clause.literal(Variable::from_index(literal.abs() as u32 - 1), literal >= 0);
        }

        num_parsed_clauses += 1;
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

// TODO: Write tests
fn skip_comments<I>(p: &mut TransposingPeekable<u8, I>) -> io::Result<()>
where
    I: Iterator<Item = io::Result<u8>>
{
    while skip_comment(p)? {
        // Do nothing
    }

    Ok(())
}

// TODO: Write tests
fn skip_comment<I>(p: &mut TransposingPeekable<u8, I>) -> io::Result<bool>
where
    I: Iterator<Item = io::Result<u8>>
{
    if let Some(_) = p.next_if_eq(&('c' as _))? {
        skip_current_line(p).map(|_| true)
    } else {
        Ok(false)
    }
}

// TODO: Write tests
fn skip_current_line<I>(p: &mut TransposingPeekable<u8, I>) -> io::Result<()>
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

// TODO: Write tests
fn expect_problem_line<I>(p: &mut TransposingPeekable<u8, I>) -> io::Result<(u32, u32)>
where
    I: Iterator<Item = io::Result<u8>>
{
    expect_char(p, 'p')?;
    skip_whitespace(p)?;
    expect_str(p, "cnf")?;
    skip_whitespace(p)?;
    let num_variables = expect_u32(p)?;
    skip_whitespace(p)?;
    let num_clauses = expect_u32(p)?;

    Ok((num_variables, num_clauses))
}

// TODO: Write tests
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

// TODO: Write tests
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

// TODO: Write tests
fn skip_whitespace<I>(p: &mut TransposingPeekable<u8, I>) -> io::Result<()>
where
    I: Iterator<Item = io::Result<u8>>
{
    while let Some(_) = p.next_if(|&b| (b as char).is_whitespace())? {
        // Do nothing
    }

    Ok(())
}

// TODO: Write tests
fn expect_u32<I>(p: &mut TransposingPeekable<u8, I>) -> io::Result<u32>
where
    I: Iterator<Item = io::Result<u8>>
{
    accept_u32(p)?.ok_or_else(|| io::Error::new(
        io::ErrorKind::InvalidData,
        "Expected unsigned 32-bit integer literal",
    ))
}

// TODO: Write tests
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

// TODO: Write tests
fn expect_i32<I>(p: &mut TransposingPeekable<u8, I>) -> io::Result<i32>
where
    I: Iterator<Item = io::Result<u8>>
{
    accept_i32(p)?.ok_or_else(|| io::Error::new(
        io::ErrorKind::InvalidData,
        "Expected signed 32-bit integer literal",
    ))
}

// TODO: Write tests
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn try_parse_i32_basic() -> io::Result<()> {
        assert_eq!(try_parse_i32_str("")?, None);
        assert_eq!(try_parse_i32_str(" ")?, None);
        assert_eq!(try_parse_i32_str("a")?, None);

        assert_eq!(try_parse_i32_str("0")?, Some(0));
        assert_eq!(try_parse_i32_str("1")?, Some(1));
        assert_eq!(try_parse_i32_str("9")?, Some(9));
        assert_eq!(try_parse_i32_str("127")?, Some(127));
        assert_eq!(try_parse_i32_str("128")?, Some(128));
        assert_eq!(try_parse_i32_str("255")?, Some(255));
        assert_eq!(try_parse_i32_str("256")?, Some(256));
        assert_eq!(try_parse_i32_str("1337")?, Some(1337));

        assert_eq!(try_parse_i32_str("-0")?, Some(0));
        assert_eq!(try_parse_i32_str("-1")?, Some(-1));
        assert_eq!(try_parse_i32_str("-9")?, Some(-9));
        assert_eq!(try_parse_i32_str("-1337")?, Some(-1337));

        assert_eq!(try_parse_i32_str("1337 and some other stuff")?, Some(1337));
        assert_eq!(try_parse_i32_str("-1337 and some other stuff")?, Some(-1337));

        assert_eq!(try_parse_i32_str(&format!("{}", i32::MAX))?, Some(i32::MAX));
        assert_eq!(try_parse_i32_str(&format!("{}", i32::MIN))?, Some(i32::MIN));
        // TODO: Test this case (and similar) properly
        //assert_eq!(try_parse_i32_str(&format!("{}", i32::MAX as i64 + 1))?, None);
        //assert_eq!(try_parse_i32_str(&format!("{}", i32::MIN as i64 - 1))?, None);

        Ok(())
    }

    fn try_parse_i32_str(s: &str) -> io::Result<Option<i32>> {
        // TODO: Consider IteratorExt with `err_forwarding_peekable` fn or something
        let mut p = TransposingPeekable::new(s.bytes().map(|b| Ok(b)));
        accept_i32(&mut p)
    }

    #[test]
    fn parse_simple() -> io::Result<()> {
        let simple = r#"p cnf 3 2
1 2 -3 0
-2 3 0"#;

        let mut formula = Formula::new();
        parse(&mut formula, io::Cursor::new(simple))?;

        // TODO: Actually validate parsed result!
        todo!()
    }
}
