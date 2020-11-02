int main()
{
	int i = 0;
	for(i = 2; i < 4; i++)
	{
		int s = sum(i, i);
		if(s != 2*i)
			goto ERROR;
	}
	
	for(i = i - 1; i >= 2; i--)
	{
		int s = sum1(i, i);
		if(s != 2 * i)
			goto ERROR;
	}

	return 0;
ERROR:
	return -1;
}

int sum(int a, int b)
{
	int c = 0;
	c = a + b;
	return c;
}
int sum1(int a, int b)
{
	int c = 0;
	c = a + b;
	return c;
}
