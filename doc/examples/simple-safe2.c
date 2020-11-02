void ldv_error_handle(int s){
	if(s > 0)
		ldv_error();
}
void ldv_error(){
LDV_ERROR:
	goto LDV_ERROR;
}
int main()
{
	int i = 5;
	int s;
	for(;i>1;i--){
		s+=i;
	}
	s = sum(i, i);
	if(s != 2 * i)
		ldv_error_handle(s);
	return 0;
}

int sum(int a, int b)
{
	int c = 0;
	c = a + b;
	return c;
}
