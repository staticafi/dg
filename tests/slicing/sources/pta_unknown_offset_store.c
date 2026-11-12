/* A store via a pointer with an unknown offset must not be a strong update
 * in the flow-sensitive pointer analysis: it may write to a different
 * element than the previous store and the value stored before must stay.
 * (The analysis used to drop &a from arr, so the slicer removed `a = 1`). */
int k = 0, m = 1;

int main(void) {
    int a, b;
    int *arr[2];
    a = 1;
    b = 2;
    arr[k] = &a;
    arr[m] = &b;
    int *p = arr[0];
    test_assert(*p == 1);
    return 0;
}
