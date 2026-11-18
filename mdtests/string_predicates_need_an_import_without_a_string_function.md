# string predicates need an import when the C program uses no string function

The negative twin of
[`a_string_function_call_brings_the_c_string_contracts.md`](a_string_function_call_brings_the_c_string_contracts.md).
The file uses the short path `string::readable` without importing
`click::c::string`. The diagnostic names the import and the full path
that can be used directly.

```c filename=string_predicates_need_an_import_without_a_string_function.c
int first(const unsigned char *text) {
    return text[0];
}
```

```click
verifying "string_predicates_need_an_import_without_a_string_function.c";

int32 first(const uint8* text) {
    requires string::readable(text);
    ensures 1 == 1;
}
```

```expect
fail: `string::readable` names Click library module `click::c::string`, which this file does not import; add `import click::c::string;` or write `click::c::string::readable`
```
