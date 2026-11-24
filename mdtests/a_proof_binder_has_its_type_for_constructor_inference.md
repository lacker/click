# A proof binder has its type for constructor inference

`List::Cons(y, List::Nil)` leaves its type argument to inference, which
reads it from `y`. A name the proof binds has its type in the tactics after
it: an `intro()` variable, under its written name or the name `let name = intro()`
gives it, and an `obtain` witness. An introduced `y` that hides a parameter
`y` of another type has the introduced type. Before, these names were
unknown to inference, which refused the constructor or took the hidden
parameter's type.

```click
theorem introduced() {
    ensures forall (y: int32) { list::contains(List::Cons(y, List::Nil), y) } by {
        intro();
        unfold(list::contains(List::Cons(y, List::Nil), y));
        close();
    }
}

theorem introduced_as(x: int64) {
    ensures forall (y: int32) { list::contains(List::Cons(y, List::Nil), y) } by {
        let z = intro();
        unfold(list::contains(List::Cons(z, List::Nil), z));
        close();
    }
}

theorem obtained() {
    requires exists (y: int32) { y == 3 };
    ensures exists (y: int32) { list::contains(List::Cons(y, List::Nil), y) } by {
        let z = obtain(exists (z: int32) { z == 3 });
        have list::contains(List::Cons(z, List::Nil), z) by {
            unfold(list::contains(List::Cons(z, List::Nil), z));
            close();
        }
        witness(z);
        close();
    }
}

theorem introduced_hides_a_parameter(y: int64) {
    ensures forall (y: int32) { list::contains(List::Cons(y, List::Nil), y) } by {
        intro();
        unfold(list::contains(List::Cons(y, List::Nil), y));
        close();
    }
}
```

```expect
pass
```
