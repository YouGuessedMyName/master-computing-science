/** TASK 1-2 */

# define BILLION 1000000000

int foo ( int [n] a) // RC(a) = 4
{
    INC_RC(a, 3); // Three references in body RC(a) = 7
    DEC_RC(a, 1); // Beta reduction RC(a) = 6
    
    /* b = modarray ( a , [0] , a [0] + 1); */
    if (RC(a) == 1) {
        b = a;
        // If you equate, then the references to a and b coincide.
    } else {
        ALLOC_INT(SIZE(a), b); COPY_DATA(a, b); // RC(b) = 1
        // If you copy, then there is one reference less to a after this.
        DEC_RC(a, 1); // RC(a) = 5
    }
    INC_RC(b, 1); // One reference in body
    DEC_RC(b, 1); // Beta reduction RC(b) = 1
    b[0] = a[0] + 1
    DEC_RC(a, 1); // One delta reduction RC(a) = 4

    /* c = modarray ( b , [1] , a [1] + 42); */
    if (RC(b) == 1) {
        c = b; // RC(c) = RC(b) = 1
    } else {
        ALLOC_INT(SIZE(b), c); COPY_DATA(b, c);
        DEC_RC(b, 1);
    }
    INC_RC(c, 2); // Two references in body RC(c) = RC(b) = 3
    DEC_RC(c, 1); // Beta reduction RC(c) = RC(b) = 2
    c[1] = a[1] + 42;
    DEC_RC(a, 1); // Delta reduction RC(a) = 3

    /* res = c[1] + c[2] */
    ALLOC_INT(1, res); // RC(res) = 1
    res = c[1] + c[2]
    DEC_RC(c, 2); // RC(c) = RC(b) = 0
    
    return res; // RC(res) = 1, RC(a) = 3
}

int bar ( int [n] a) // RC(a) = 1
{
    INC_RC(a, 4); // Four occurences
    DEC_RC(a, 1); // Beta reduction
    // RC(a) = 4

    if ( foo (a) == 44 ) // RC(a) = 3
    { 
        DEC_RC(a, 2); // Two occurences in other branch RC(a) = 1
        ALLOC_INT(1, res); // RC(res) = 1
        res = a [22];
        DEC_RC(a, 1); // Delta reduction RC(a) = 0
    }
    else { 
        DEC_RC(a, 1); // One occurence in other branch RC(a) = 2
        ALLOC_INT(1, res); // RC(res) = 1
        res = a [2] + a [14]; 
        DEC_RC(a, 2); // Delta reduction RC(a) = 0
    }
    return res; // RC(res) = 1, RC(a) = 0
}

int main () {
    /* a = genarray ( [ BILLION ], 0); */
    ALLOC_INT(BILLION, a); // RC(a) = 1
    for (int i = 0; i < BILLION; i++) {
        a[i] = 0;
    }
    x = bar (a ); // RC(a) = 0, RC(x) = 1
    return x; // RC(x) = 1
} // I guess I have to assume that the compiler frees the return value of main?

//* TASK 3 */

# define BILLION 1000000000

int foo ( int [n] a) // RC(a) = n
{
    /* b = modarray ( a , [0] , a [0] + 1); */
    ALLOC_INT(SIZE(a), b); COPY_DATA(a, b); // RC(b) = 1
    b[0] = a[0] + 1
    // RC(a) = n (optimized incrementing and decrementing away,
    // this preserves semantics since n >= 1)

    /* c = modarray ( b , [1] , a [1] + 42); */
    c = b; // RC(c) = RC(b) = 1
    INC_RC(c, 1); // RC(c) = RC(b) = 2
    c[1] = a[1] + 42;
    DEC_RC(a, 1); // Delta reduction RC(a) = n-1

    /* res = c[1] + c[2] */
    ALLOC_INT(1, res); // RC(res) = 1
    res = c[1] + c[2]
    DEC_RC(c, 2); // RC(c) = RC(b) = 0
    
    return res; // RC(res) = 1, RC(a) = n-1
}

int bar ( int [n] a) // RC(a) = n
{
    INC_RC(a, 2); // RC(a) = n+2
    ALLOC_INT(1, res); // RC(res) = 1

    if ( foo (a) == 44 ) // RC(a) = n+2
    { 
        DEC_RC(a, 1); // RC(a) = n
        res = a [22];
        DEC_RC(a, 1); //RC(a) = n-1
    }
    else { 
        res = a [2] + a [14]; 
        DEC_RC(a, 2); // RC(a) = n-1
    }
    return res; // RC(res) = 1, RC(a) = n-1
}

int main () {
    /* a = genarray ( [ BILLION ], 0); */
    ALLOC_INT(BILLION, a); // RC(a) = 1

    x = bar (a ); // RC(a) = 0, RC(x) = 1
    return x;
}

/** TASK 4
It would be possible to get rid of all reference counting,
but then you would require some JVM-like garbage collection mechanism to prevent
memory leaks. */