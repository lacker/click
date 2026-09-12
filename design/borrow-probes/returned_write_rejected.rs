pub struct Pair {
    pub left: i32,
    pub right: i32,
}

pub fn left(p: &mut Pair) -> &mut i32 {
    &mut p.left
}

pub fn returned_write(p: &mut Pair) -> i32 {
    let q = left(p);
    p.left = 8;
    *q
}
