\predicates {
  /* Declare predicates occurring in the problem */  

  divides(int, int);
}

\problem {
  /* Problem to be proven. The implicit quantification is:
   *    \exists <existentialConstants>; \forall <predicates>; ... */

     \forall int x; divides(x, 0)
  -> \forall int x, y; (divides(x, y) -> divides(x, y+x) & divides(x, y-x))
  ->
     \exists int x; (divides(x, 8) & divides(x, 12) & x > 0)
}
