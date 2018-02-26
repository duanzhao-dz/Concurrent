\predicates {
}
\functions {
int c___dollar_file__main__1__x_at__hash_1;
int c___dollar_file__main__1__x_at__hash_2;
int sum;
}

\problem {
  \part[part00000] (
( ( c___dollar_file__main__1__x_at__hash_1 < 128 ) & (! ( c___dollar_file__main__1__x_at__hash_1 < -128 ) ) )
&
 ( c___dollar_file__main__1__x_at__hash_1 < 10 ) & ( ( c___dollar_file__main__1__x_at__hash_1 < 0 ) | ( c___dollar_file__main__1__x_at__hash_1 = 0 ) ) )
     ->
  \part[part00001] (
( ( c___dollar_file__main__1__x_at__hash_2 < 128 ) & (! ( c___dollar_file__main__1__x_at__hash_2 < -128 ) ) )
&


\exists int sum_div; 256 * sum_div + sum = 1 + c___dollar_file__main__1__x_at__hash_1

/*
    (sum = 1 + c___dollar_file__main__1__x_at__hash_1 |
     sum = 1 + c___dollar_file__main__1__x_at__hash_1 + 256 |
     sum = 1 + c___dollar_file__main__1__x_at__hash_1 - 256)
*/
&
(! ( sum < -128 ) ) & ( sum < 128 )


&
 ( c___dollar_file__main__1__x_at__hash_2 = c___dollar_file__main__1__x_at__hash_2 ) &
 ( sum = c___dollar_file__main__1__x_at__hash_2 ) &
 ( sum = sum ) &
 ( c___dollar_file__main__1__x_at__hash_2 = sum ) )
     ->
  \part[part00002] true
     ->
  \part[part00003] (! ( c___dollar_file__main__1__x_at__hash_2 < 10 ) )
     ->
  \part[part00004] false
}
\interpolant{part00000;part00001,part00002,part00003,part00004}
\interpolant{part00000,part00001;part00002,part00003,part00004}
\interpolant{part00000,part00001,part00002;part00003,part00004}
\interpolant{part00000,part00001,part00002,part00003;part00004}
