// Original constructor contracts shared by the public checksum boundaries.
impl Default for adler2::Adler32 {
    fn default() -> adler2::Adler32 {
     ensures result.a == 1;
     ensures result.b == 0;
    } by { execute(); simp(); }
}

impl adler2::Adler32 {
    fn new() -> adler2::Adler32 {
     ensures result.a == 1;
     ensures result.b == 0;
    } by { execute(); simp(); }
}
