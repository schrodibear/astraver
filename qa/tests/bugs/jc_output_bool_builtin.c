/*@ ghost extern int __task_capable; */
/*@ axiomatic task_capable {
    logic 𝔹 capable{L}(ℤ n)
         reads __task_capable;
    }
*/


int
main(int argc, char **argv)
{
	//@ assert capable(1) == \true;
	return 0;
}

