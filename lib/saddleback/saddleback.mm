>> m,n:N+. B:({0..(m-1)}->{0..(n-1)}->Int) where sorted(B{m,n}). x:Int.
      x  B{m,n}(0:(m-1), 0:(n-1))  (x  B{m,n}(0:(m-1), 0:(n-1)))
|   BY (Idtac ...)
|      THEN 
|      (InstantiateLemma `saddleback_lemma` 
|       ['m'; 'n'; 'B'; 'x'; 'm+n-1'; 'm-1'; '0'] ...)
|   1. m:Int
|   2. 0<m
|   3. n:Int
|   4. 0<n
|   5. B:{0..(m-1)}->{0..(n-1)}->Int
|   6. x:Int
|   7. 0 in int
|   8. sorted(B{m,n})
|   9. m,n:N+. B:({0..(m-1)}->{0..(n-1)}->Int) where sorted(B{m,n}). x:Int.
|         k:N. i:{0..(m-1)}. j:{0..(n-1)} where i+(n-j) = k.
|           x  B{m,n}(0:i, j:(n-1))  (x  B{m,n}(0:i, j:(n-1)))
|   10. m+n-1<0
|-  >> void
|   |   BY (ref `monotonicity 2+4` ...)
