use std::cell::Cell;
use std::mem::MaybeUninit;

pub fn shared_then_write(p: &mut i32) -> i32 {
    let q = &*p;
    let before = *q;
    *p = 7;
    before
}

pub fn mutable_reborrow(p: &mut i32) -> i32 {
    let q = &mut *p;
    *q = 7;
    *p = 8;
    *p
}

pub struct Pair {
    pub left: i32,
    pub right: i32,
}

pub fn left(p: &mut Pair) -> &mut i32 {
    &mut p.left
}

pub fn returned_borrow(p: &mut Pair) {
    let q = left(p);
    *q = 7;
    p.right = 8;
}

pub fn split_borrow(p: &mut [i32]) {
    let (left, right) = p.split_at_mut(1);
    left[0] = 7;
    right[0] = 8;
}

pub fn shared_cell(p: &Cell<i32>, q: &Cell<i32>) -> i32 {
    p.set(7);
    q.get()
}

pub fn initialize(p: &mut MaybeUninit<i32>) -> &mut i32 {
    p.write(7)
}

pub struct Guard<'a>(&'a mut i32);

impl Drop for Guard<'_> {
    fn drop(&mut self) {
        *self.0 = 9;
    }
}

pub fn early_return(early: bool, p: &mut i32) -> i32 {
    let _guard = Guard(p);
    if early {
        return 1;
    }
    2
}

fn main() {
    let mut x = 3;
    assert_eq!(shared_then_write(&mut x), 3);
    assert_eq!(x, 7);
    assert_eq!(mutable_reborrow(&mut x), 8);
    let mut pair = Pair { left: 0, right: 0 };
    returned_borrow(&mut pair);
    assert_eq!((pair.left, pair.right), (7, 8));
    let mut values = [0, 0];
    split_borrow(&mut values);
    assert_eq!(values, [7, 8]);
    let cell = Cell::new(0);
    assert_eq!(shared_cell(&cell, &cell), 7);
    let mut slot = MaybeUninit::uninit();
    assert_eq!(*initialize(&mut slot), 7);
    assert_eq!(early_return(true, &mut x), 1);
    assert_eq!(x, 9);
    x = 0;
    assert_eq!(early_return(false, &mut x), 2);
    assert_eq!(x, 9);
}
