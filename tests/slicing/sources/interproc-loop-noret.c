/*
 * Test: code after a call to a function-with-a-loop must be kept in the slice.
 *
 * Without the fix, the slicer may drop test_assert() because looping_callee()
 * is not recognised as potentially noret.
 * With the fix, looping_callee() has a noret loop header, so the call site
 * creates an interprocedural control dependency that retains test_assert().
 */

extern int __VERIFIER_nondet_int(void);

void looping_callee(void) {
    /* loop exists => may not terminate => noret in the interproc fix */
    while (__VERIFIER_nondet_int()) { }
}

int main(void) {
    looping_callee();
    test_assert(1);   /* must survive slicing */
    return 0;
}
