use std::io;
use std::iter::Iterator;

pub struct TransposingPeekable<Item, I>
where
    I: Iterator<Item = io::Result<Item>>,
{
    iter: I,
    peeked: Option<Option<Item>>,
}

impl<Item, I> TransposingPeekable<Item, I>
where
    I: Iterator<Item = io::Result<Item>>,
{
    fn new(iter: I) -> TransposingPeekable<Item, I> {
        TransposingPeekable { iter, peeked: None }
    }

    pub fn next(&mut self) -> io::Result<Option<Item>> {
        match self.peeked.take() {
            Some(peeked) => Ok(peeked),
            None => self.iter.next().transpose(),
        }
    }

    pub fn next_if(&mut self, func: impl FnOnce(&Item) -> bool) -> io::Result<Option<Item>> {
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

    pub fn next_if_eq<T>(&mut self, expected: &T) -> io::Result<Option<Item>>
    where
        Item: PartialEq<T>,
    {
        self.next_if(|next| next == expected)
    }
}

pub trait TransposingPeekableIteratorExt<Item, I>
where
    Self: Sized,
    I: Iterator<Item = io::Result<Item>>,
{
    fn transposing_peekable(self) -> TransposingPeekable<Item, I>;
}

impl<Item, I> TransposingPeekableIteratorExt<Item, I> for I
where
    Self: Sized,
    I: Iterator<Item = io::Result<Item>>,
{
    fn transposing_peekable(self) -> TransposingPeekable<Item, I> {
        TransposingPeekable::new(self)
    }
}
