/* Generated by CIL v. 1.3.7 */
/* print_CIL_Input is true */

#line 2 "test/tests/single/struct_copy_BUG.c"
struct s {
   int x ;
};
#line 3 "test/tests/single/struct_copy_BUG.c"
int main(void) 
{ struct s a ;
  struct s b ;
  int a_x3 ;
  int b_x4 ;

  {
#line 6
  a_x3 = 4;
#line 7
  b_x4 = 8;
#line 8
  a_x3 = b_x4;
#line 9
  if (a_x3 == 8) {
    ERROR: 
    goto ERROR;
  } else {

  }
#line 13
  return (0);
}
}
