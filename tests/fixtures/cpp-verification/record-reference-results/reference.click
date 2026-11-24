verifying "reference.cpp";
Widget& Outer::get() { views this->first; views this->child.value; ensures &result == &this->child; }
Widget& child(Outer& outer) { views outer.first; views outer.child.value; ensures &result == &outer.child; }
int32 probe(Outer& outer, int32 value) { owns outer.child.value; views outer.first; ensures result == value; ensures outer.child.value == value; ensures outer.first == old(outer.first); } by {
    step(); step(); step();
    have &ref == &outer.child by { close(); }
    have separate(memory(outer.child.value), memory(outer.first)) by { close(); }
    step() by {
        rewrite(&ref, &outer.child);
        close();
    }
}
