# Qualified static arrays and struct fields retain their layout

```c filename=storage.c
struct pair { int first; int second; };
void clear(void) {
    static int cells[2][3] = {{1,2,3},{4,5,6}};
    static struct pair value = {7,8};
    cells[1][2] = 0;
    value.second = 0;
}
int main(void) { clear(); return 0; }
```

```click
verifying "storage.c" as storage;
void clear() {
    owns storage::clear::cells[1][2..3];
    owns storage::clear::value.second;
    ensures storage::clear::cells[1][2] == 0;
    ensures storage::clear::value.second == 0;
} by { execute(); simp(); }
int main() {
    ensures storage::clear::cells[0][2] == 3;
    ensures storage::clear::cells[1][1] == 5;
    ensures storage::clear::value.first == 7;
    ensures storage::clear::value.second == 0;
} by { execute(); simp(); }
```

```expect
pass
```
