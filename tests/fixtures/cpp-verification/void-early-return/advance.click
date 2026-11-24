verifying "advance.cpp";

void advance(bool empty, int32& cursor) {
    owns cursor;
    ensures empty implies cursor == old(cursor);
    ensures not empty implies cursor == 7;
} by {
    if empty {
        step_until(function.exit);
        have empty implies cursor == old(cursor) by {
            intro();
            close();
        }
        have not empty implies cursor == 7 by {
            intro();
            contradiction(not empty);
        }
    } else {
        step_until(function.exit);
        have empty implies cursor == old(cursor) by {
            intro();
            contradiction(empty);
        }
        have not empty implies cursor == 7 by {
            intro();
            close();
        }
    }
}
