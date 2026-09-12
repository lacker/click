pub fn shared_write(p: &mut i32) -> i32 {
    let q = &*p;
    *p = 7;
    *q
}
