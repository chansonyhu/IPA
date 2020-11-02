void ldv_error(){
ERROR:
	goto ERROR;
}
int main()
{
	int i = 5;
	int s;
	s = sum(i, i);
	if(s != 2 * i)
		ldv_error();
	return 0;
}

int sum(int a, int b)
{
	int c = 0;
	c = a + b;
	return c;
}
