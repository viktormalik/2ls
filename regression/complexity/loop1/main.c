void main()
{
  unsigned __CPROVER_CPLX_CNT_main = 0;
  int x = 0;  

  while(x<10)
  {
    ++x;
    assert(x<=10);
    __CPROVER_CPLX_CNT_main++;
  }

  assert(x==10);
}
