void ldv_error(){
LDV_ERROR:
	goto LDV_ERROR;
}
int main()
{
	int i = 5;
	int s;
	s = sum(i, i);
	if(s != 2 * i + 1)
		ldv_error();
	return 0;
}

int sum(int a, int b)
{
	int c = 0;
	c = a + b;
	return c;
}
