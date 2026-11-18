import click::option;

// Rust's `Option::unwrap_or`: the payload of `Some`, else `default`. A call
// of the method in imported Rust is a call to an external function whose
// contract states its result with this function.
function unwrap_or<T>(o: Option<T>, default: T) -> T {
    match o {
        Option::Some(value) => value,
        Option::None => default,
    }
}
