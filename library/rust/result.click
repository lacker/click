import click::result;

// Rust's `Result::unwrap_or`: the payload of `Ok`, else `default`. A call of
// the method in imported Rust is a call to an external function whose
// contract states its result with this function.
function unwrap_or<T, E>(r: Result<T, E>, default: T) -> T {
    match r {
        Result::Ok(value) => value,
        Result::Err(error) => default,
    }
}
