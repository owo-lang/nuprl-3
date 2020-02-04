>> m,n:N. B:({0..(m-1)}->{0..(n-1)}->Int). i,j,p,q:Int. x:Int. U1
|   BY RepeatUntil (\p. concl p = 'U1') Intro
|      THEN IfThen is_wf_goal Autotactic
|   1. m:N
|   2. n:N
|   3. B:{0..(m-1)}->{0..(n-1)}->Int
|   4. i:Int
|   5. j:Int
|   6. p:Int
|   7. q:Int
|   8. x:Int
|-  >> U1
|   |   BY (Refine (explicit_intro 
|   |      'r:{0..(m-1)}. s:{0..(n-1)}
|   |          where B(r,s) = x & i  r  p & j  s  q' )
|   |       ...)
