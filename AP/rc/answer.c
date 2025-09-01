#define BILLION 1000000000

// RC(a) = n
int foo (int[n] a)
{
    INC_RC(a, 2); // RC(a) = n + 2 (+3 refs, -1 consumed)
    /* b = modarray( a, [0], a[0] + 1); */
    ALLOC_INT(SIZE(a), b); // RC(b) = 1
    COPY_DATA(SIZE(a), a, b);
    DEC_RC(a, 2); // RC(a) = n

    /* c = modarray( b, [1], a[1] + 42); */
    c = b; // RC(c) = RC(b) = 1
    INC_RC(c, 1); // RC(b) = RC(c) = 2 (+ 2 refs c -1 ref b)
    c[1] = a[1] + 42;
    DEC_RC(a, 1); // RC(a) = n-1
    res = c[1] + c[2];
    DEC_RC(c, 2); // RC(b) = RC(c) = 0;
    return res;
} // RC(a) = n

// RC(a) = n
int bar (int[n] a)
{ 
    INC_RC(a, 2); // RC(a) = n+2
    if (foo (a) == 44) 
    { 
        res = a[22];
        DEC_RC(a, 1); // RC(a) = n+1
    } 
    else 
    { 
        res = a[2] + a[14];
        DEC_RC(a, 2); // RC(a) = n-1
    }
    return res;
}

int main() 
{
    a = genarray ( [BILLION], 0);
    //RC(a) = 1
    x = bar (a);
    //RC(a) = 0
    return x;
}