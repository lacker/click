pub fn parent_write(p: &mut i32) -> i32 {
    let q = &mut *p;
    *p = 7;
    *q
}
