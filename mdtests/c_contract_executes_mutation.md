# Explicit callback execution: mutation

```click
resource Buffer(data: int32*) { owns data[0..1]; }
contract void Raw(int32* data) {
 requires data[0] < 100;
 owns data[0..1];
 ensures data[0] == old(data[0]) + 1;
}
contract void Buffered(int32* data) {
 requires data[0] < 100;
 owns Buffer(data);
 ensures data[0] > old(data[0]);
}
theorem lift(callback: void (*)(int32*)) executes callback(int32* cell) {
 requires Raw(callback);
 ensures Buffered(callback) by {
 unfold(Buffer(cell)); step(Raw);
 apply(int32_increment_strictly_increases(old(cell[0]), 100));
 have cell[0] > old(cell[0]) by {
     rewrite(cell[0] == old(cell[0]) + 1);
     assumption();
 }
 fold(Buffer(cell)); simp();
 }
}
```

```expect
pass
```
