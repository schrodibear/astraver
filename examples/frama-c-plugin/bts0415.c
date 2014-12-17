
// avoids reference to earlier assertions

void ftest8(void)
{
    // unprovable:
    //@ assert -2147483648 <= 0;
}

void ftest7(void)
{
    // unprovable:
    //@ assert -2147483647 <= 0;
}

void ftest6(void)
{
    // provable:
    //@ assert -2147483646 <= 0;
}



// previous attempt to avoid references:

void ftest(int n)
{
    switch (n) {
    case 8:
	// unprovable:
	//@ assert -2147483648 <= 0;
	break;
    case 7:
	// provable:
	//@ assert -2147483647 <= 0;
	break;
    case 6:
	// provable:
	//@ assert -2147483646 <= 0;
	break;
    }
}

