int imported_helper(int x) { return x; }
int imported_caller(int x) { return imported_helper(x); }
void imported_keep(int *p) {}
void imported_resource_caller(int *p) { imported_keep(p); }
