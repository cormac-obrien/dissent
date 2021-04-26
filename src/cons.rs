//! A bump-allocated, append-only singly-linked list.

use std::{cell::Cell, fmt};

use bumpalo::Bump;

#[derive(Clone, Debug, PartialEq, Eq)]
struct ConsCell<'a, T> {
    val: T,
    tail: Cell<Option<&'a ConsCell<'a, T>>>,
}

impl<'a, T> ConsCell<'a, T> {
    fn new_with_tail(val: T, tail: Option<&'a ConsCell<'a, T>>) -> Self {
        ConsCell {
            val,
            tail: Cell::new(tail),
        }
    }
}

/// A bump-allocated, append-only singly-linked list.
#[derive(Clone)]
pub struct ConsList<'bump, T> {
    bump: &'bump Bump,
    head: Cell<Option<&'bump ConsCell<'bump, T>>>,
    last: Cell<Option<&'bump ConsCell<'bump, T>>>,
}

impl<'bump, T> ConsList<'bump, T> {
    /// Initializes an empty cons list with the given allocator.
    pub fn new_in(bump: &'bump Bump) -> Self {
        ConsList {
            bump,
            head: Cell::new(None),
            last: Cell::new(None),
        }
    }

    #[doc(hidden)]
    pub fn with_head_and_tail(head: T, tail: ConsList<'bump, T>) -> Self {
        let ConsList {
            bump,
            head: old_head,
            last,
        } = tail;

        ConsList {
            bump,
            head: Cell::new(Some(
                bump.alloc(ConsCell::new_with_tail(head, old_head.get())),
            )),
            last,
        }
    }

    /// Inserts a new element at the end of the list.
    pub fn push(&mut self, val: T) {
        let new_cell = self.bump.alloc(ConsCell {
            val,
            tail: Cell::new(None),
        });

        if let Some(ref mut last) = self.last.take() {
            debug_assert!(self.head.get().is_some());
            last.tail.set(Some(new_cell));
        } else {
            debug_assert!(self.head.get().is_none());
            self.head.set(Some(new_cell));
        }

        self.last.set(Some(new_cell));
    }

    /// Returns an iterator over the list.
    pub fn iter(&self) -> ConsListIterator<'bump, T> {
        ConsListIterator {
            next: self.head.get(),
        }
    }
}

impl<'bump, T: fmt::Debug> fmt::Debug for ConsList<'bump, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<'bump, T: PartialEq> PartialEq for ConsList<'bump, T> {
    fn eq(&self, other: &Self) -> bool {
        self.head.get() == other.head.get() && self.last.get() == other.last.get()
    }
}

impl<'bump, T: Eq> Eq for ConsList<'bump, T> {}

/// Initializes a cons list with a bump allocator and a list of elements.
///
/// ## Example
/// ```
/// # use bumpalo::Bump;
/// # use dissent::cons_list_in;
/// # fn main () {
/// let bump = Bump::new();
/// let list = cons_list_in!(&bump, ["hello", "goodbye"]);
///
/// let mut it = list.iter();
/// assert_eq!(it.next(), Some(&"hello"));
/// assert_eq!(it.next(), Some(&"goodbye"));
/// assert!(it.next().is_none());
/// # }
/// ```
#[macro_export]
macro_rules! cons_list_in {
    ( $bump:expr , [] $(,)? ) => {
        $crate::ConsList::new_in($bump)
    };

    ( $bump:expr , [$head:expr $(,)?] $(,)? ) => {
        {
            let mut list = $crate::ConsList::new_in($bump);
            list.push($head);
            list
        }
    };

    ( $bump:expr , [ $head:expr , $($tail:expr),* $(,)?] $(,)?) => {
        $crate::ConsList::with_head_and_tail($head, cons_list_in!($bump, [$($tail),*]))
    };
}

/// An iterator over a `ConsList`.
pub struct ConsListIterator<'a, T> {
    next: Option<&'a ConsCell<'a, T>>,
}

impl<'a, T> Iterator for ConsListIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.next.take() {
            Some(ConsCell { val, tail, .. }) => {
                self.next = tail.get().map(|t| &*t);
                Some(val)
            }
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cons_list() {
        let bump = Bump::new();

        let empty: ConsList<u32> = ConsList::new_in(&bump);
        let mut empty_it = empty.iter();
        assert!(empty_it.next().is_none());

        let mut one_elem = ConsList::new_in(&bump);
        one_elem.push(1u32);
        let mut one_elem_it = one_elem.iter();
        assert_eq!(one_elem_it.next().copied(), Some(1));
        assert!(one_elem_it.next().is_none());

        let mut multi_elem = ConsList::new_in(&bump);
        multi_elem.push(1u32);
        multi_elem.push(2u32);
        multi_elem.push(3u32);
        let mut multi_elem_it = multi_elem.iter();
        assert_eq!(multi_elem_it.next().copied(), Some(1));
        assert_eq!(multi_elem_it.next().copied(), Some(2));
        assert_eq!(multi_elem_it.next().copied(), Some(3));
        assert!(multi_elem_it.next().is_none());
    }

    #[test]
    fn test_cons_list_in() {
        let bump = Bump::new();
        let cons = cons_list_in!(&bump, [1u32, 2, 3]);
        let mut it = cons.iter().copied();
        assert_eq!(it.next(), Some(1));
        assert_eq!(it.next(), Some(2));
        assert_eq!(it.next(), Some(3));
        assert_eq!(it.next(), None);
    }
}
