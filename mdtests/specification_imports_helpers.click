verifying "specification_imports_helpers.c";

contract int32 ImportedIdentity(int32 x) {
    ensures result == x;
}

int32 imported_helper(int32 x) {
    ensures result == x by { execute(); simp(); }
}

tactic retain_equal(x: int32, y: int32) {
    requires x == y;
    ensures x == y;
} by { have x == y by assumption(); }

resource imported_cell(p: int32*) {
    field value: int32;
    owns *p;
    fact *p == value;
}

void imported_keep(int32* p) {
    consumes before: imported_cell(p);
    produces after: imported_cell(p);
    ensures after.value == old(before.value);
} by {
    unfold(before);
    execute();
    let after = fold(imported_cell(p), { value: *p });
    simp();
}

tactic imported_rename(p: int32*) {
    consumes before: imported_cell(p);
    produces after: imported_cell(p);
    ensures after.value == old(before.value);
} by {
    unfold(before);
    let after = fold(imported_cell(p), { value: *p });
}
