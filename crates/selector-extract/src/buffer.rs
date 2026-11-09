//! Small transient argument/child lists stay on the stack. Only unusually large
//! arities allocate; final variable-length records move into flat owned tables.
use std::ops::{Deref, DerefMut};
pub(crate) struct Buffer<T: Default, const N: usize = 8> {
    inline: [T; N],
    spill: Vec<T>,
    len: usize,
}
impl<T: Default, const N: usize> Buffer<T, N> {
    pub fn new() -> Self {
        Self {
            inline: std::array::from_fn(|_| T::default()),
            spill: Vec::new(),
            len: 0,
        }
    }
    pub fn with_capacity(capacity: usize) -> Self {
        let mut out = Self::new();
        if capacity > N {
            out.spill = Vec::with_capacity(capacity);
        }
        out
    }
    pub fn push(&mut self, value: T) {
        if self.len < N && self.spill.capacity() == 0 {
            self.inline[self.len] = value;
        } else {
            if self.spill.capacity() == 0 {
                self.spill = Vec::with_capacity(N * 2);
                for value in &mut self.inline {
                    self.spill.push(std::mem::take(value));
                }
            }
            self.spill.push(value);
        }
        self.len += 1;
    }
    pub fn resize(&mut self, length: usize, value: T)
    where
        T: Clone,
    {
        while self.len < length {
            self.push(value.clone());
        }
    }
}
impl<T: Default, const N: usize> Deref for Buffer<T, N> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        if self.spill.capacity() == 0 {
            &self.inline[..self.len]
        } else {
            &self.spill
        }
    }
}
impl<T: Default, const N: usize> DerefMut for Buffer<T, N> {
    fn deref_mut(&mut self) -> &mut [T] {
        if self.spill.capacity() == 0 {
            &mut self.inline[..self.len]
        } else {
            &mut self.spill
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn common_arities_do_not_allocate_and_spill_preserves_order() {
        let mut buffer = Buffer::<u32, 8>::new();
        for n in 0..8 {
            buffer.push(n);
        }
        assert_eq!(buffer.spill.capacity(), 0);
        buffer.push(8);
        buffer.resize(11, 99);
        assert_eq!(&*buffer, &[0, 1, 2, 3, 4, 5, 6, 7, 8, 99, 99]);
        buffer[3] = 42;
        assert_eq!(buffer[3], 42);
        let mut large = Buffer::<u32, 8>::with_capacity(12);
        large.push(3);
        assert_eq!(&*large, &[3]);
    }
}
