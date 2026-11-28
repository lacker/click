verifying "returns.rs";

// A slice result is one slice: a contract reads `result.len()` and
// `result.as_ptr()`, as it does a slice parameter's.
fn slice_returns::whole(bytes: &[u8]) -> &[u8] {
    ensures result.len() == bytes.len();
    ensures result.as_ptr() == bytes.as_ptr();
}

// A call passes the slice on and returns the slice it receives.
fn slice_returns::passed(bytes: &[u8]) -> &[u8] {
    ensures result.len() == bytes.len();
    ensures result.as_ptr() == bytes.as_ptr();
}

// A caller binds the result as one slice local.
fn slice_returns::measured(bytes: &[u8]) -> usize {
    ensures result == bytes.len();
} by {
    // A proof reads the slice local where it was live.
    step_until(function.exit);
    have at(statement(0).exit, view.as_ptr()) == bytes.as_ptr();
    have at(statement(0).exit, view.len()) == bytes.len();
    close();
}

// A contract indexes a slice result as it does a slice parameter.
fn slice_returns::same(bytes: &[u8]) -> &[u8] {
    requires 0u64 < bytes.len();
    views *bytes;
    ensures result[0] == bytes[0];
}

fn slice_returns::exclusive(bytes: &mut [u8]) -> &mut [u8] {
    ensures result.len() == bytes.len();
    ensures result.as_ptr() == bytes.as_ptr();
}

fn slice_returns::named(s: &str) -> &str {
    ensures result.len() == s.len();
    ensures result.as_ptr() == s.as_ptr();
}

// A proof reads an element through a slice local where it was live, at the
// slice's element type.
fn slice_returns::copied(bytes: &[u8]) -> u8 {
    requires 0u64 < bytes.len();
    views *bytes;
    ensures result == bytes[0];
} by {
    step_until(function.exit);
    have at(statement(0).exit, view[0]) == bytes[0];
    close();
}

// A caller reads an element through the slice a call returned, `view[0]`:
// it is the argument's element.
fn slice_returns::first(bytes: &[u8]) -> u8 {
    requires 0u64 < bytes.len();
    views *bytes;
    ensures result == bytes[0];
}
