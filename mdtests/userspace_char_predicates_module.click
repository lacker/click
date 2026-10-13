// A module of definitions spells plain `char` without a target of its own:
// it is checked where it is imported, under the importer's C target.
predicate negative_char(c: char) {
    c < 0
}
