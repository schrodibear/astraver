
short ValueA;
/*@ invariant tev: 0 <= ValueA <= 10*/
short ValueB;
/*@ invariant ev: 0 <= ValueB <= 10*/
short returnValue;
/*@ invariant eev: 0 <= returnValue <= 10*/


/*@ 
  @ assigns returnValue
  @ ensures \result >= 0
  */
short test1(void)
{	
	returnValue = ValueA & ValueB;

	return returnValue;
}

/*@ 
  @ assigns returnValue
  @ ensures \result >= 0
  */
short test2(void)
{	
	returnValue = ValueA & ValueB;

	if((returnValue < 0) || (returnValue > 10))
	{
		returnValue = 0;
	}
	
	return returnValue;
}

/*@ 
  @ assigns returnValue
  @ ensures \result >= 0
  */
short test3(void)
{	
	returnValue = returnValue;

	return returnValue;
}

