# define BILLION 1000000000

int foo ( int [n] a)
{
    INC_RC(a, 3); // Three references in body
    DEC_RC(a, 1); // Beta reduction
    
    /* b = modarray ( a , [0] , a [0] + 1); */
    if (RC(a) == 1) {
        b = a;
    } else {
        ALLOC_INT(SIZE(a), b); COPY_DATA(a, b);
    }
    INC_RC(b, 1); // One reference in body
    DEC_RC(b, 1); // Beta reduction
    b[0] = a[0] + 1
    DEC_RC(a, 2); // Two delta reductions

    /* c = modarray ( b , [1] , a [1] + 42); */
    if (RC(b) == 1) {
        c = b;
    } else {
        ALLOC_INT(SIZE(b), c); COPY_DATA(b, c);
    }
    INC_RC(c, 2); // Two references in body
    DEC_RC(c, 1); // Beta reduction
    c[1] = a[1] + 42;
    DEC_RC(a, 1); // Delta reduction
    DEC_RC(b, 1); // Delta reduction

    /* res = c[1] + c[2] */
    ALLOC_INT(1, res);
    DEC_RC(c, 2);
    res = c[1] + c[2]
    
    return res;
}

int bar ( int [n] a)
{
    INC_RC(a, 1); // One occurence in if-statement.
    DEC_RC(a, 1); // Beta reduction

    DEC_RC(a, 1);
    if ( foo (a) == 44 )
    { 
        INC_RC(a, 1); DEC_RC(a, 1);
        ALLOC_INT(1, res);
        res = a [22]; 
    }
    else { 
        INC_RC(a, 2); DEC_RC(a, 2);
        ALLOC_INT(1, res);
        res = a [2] + a [14];
    }
    return res;
}

int main () {
    /* a = genarray ( [ BILLION ], 0); */
    ALLOC_INT(BILLION, a);
    for (int i = 0; i < BILLION; i++) {
        a[i] = 0;
    }
    /* x = bar (a ); */
    ALLOC_INT(x, 1);
    DEC_RC(a, 1);
    return x;
}