int main() {
  int i = 0;
  int a = 0;

  while (1) {
    if (i == 20) {
       goto LOOPEND;
    } else {
       i++;
       a++;
    }

    if (i != a) {
      goto LDV_ERROR;
    }
  }

  LOOPEND:

  if (a != 20) {
     goto LDV_ERROR;
  }

  return (0);
  LDV_ERROR:
  return (-1);
}

