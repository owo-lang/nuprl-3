>> m,n:N. B:({0..(m-1)}->{0..(n-1)}->Int). U1
|   BY RepeatUntil (\p. concl p = 'U1') Intro
|      THEN IfThen is_wf_goal Autotactic
|      
|   1. m:N
|   2. n:N
|   3. B:{0..(m-1)}->{0..(n-1)}->Int
|-  >> U1
|   |   BY (Refine (explicit_intro 
|   |      'j:{0..(n-1)}. i,p:{0..(m-1)}. i<p => B(i,j)  B(p,j) 
|   |      & i:{0..(m-1)}. j,q:{0..(n-1)}. j<q => B(i,j)  B(i,q) ' ) ...)
