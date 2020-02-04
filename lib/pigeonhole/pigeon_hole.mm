>> n:N. f:{1..(n+1)}->{1..n}. 
     i,j:{1..(n+1)} where i<j & f(i)=f(j)
|   BY (InductionOn `n` `k` ...)
|   1. f:{1..(((0))+1)}->{1..((0))}
|-  >> i,j:{1..(((0))+1)} where i<j & f(i)=f(j)
|   |   BY (Properties ['f(1)'] ...)
|   1. k:int
|   2. 0<k
|   3. f:{1..(((k-1))+1)}->{1..((k-1))}. 
|        i,j:{1..(((k-1))+1)} where i<j & f(i)=f(j)
|   4. f:{1..(((k))+1)}->{1..((k))}
|-  >> i,j:{1..(((k))+1)} where i<j & f(i)=f(j)
|   |   BY (
|   |      CaseLemma `finite_function_decidability`
|   |      [ 'k'; 'k'; 'ˆx.f(x)'; 'f(k+1)' ] ...)
|   |   5. x:Int
|   |   6. (1)(x)(k)
|   |   7. (ˆx.f(x))(x)=f(k+1) in {1..(k)}
|   |-  >> i,j:{1..(((k))+1)} where i<j & f(i)=f(j)
|   |   |   BY (Reduce
|   |   |       THEN (ElimEquality 7 ...)
|   |   |       THEN IntroTerms ['x'; 'k+1']
|   |   |       ...)
|   |   5. x:{1..(k)}. ((ˆx.f(x))(x)=(f(k+1)) in {1..(k)})
|   |-  >> i,j:{1..(((k))+1)} where i<j & f(i)=f(j)
|   |   |   BY (ElimOn 3 
|   |   |       'ˆx. if f(x)=k then f(k+1) else f(x)' ...)
|   |   |   6. x:Int
|   |   |   7. (1)(x)((k-1)+1)
|   |   |   8. f(x)=k in int
|   |   |   9. f(k+1)<1
|   |   |-  >> void
|   |   |   |   BY (Properties ['f(k+1)'] ...)
|   |   |   6. x:Int
|   |   |   7. (1)(x)((k-1)+1)
|   |   |   8. f(x)=k in int
|   |   |   9. k-1<f(k+1)
|   |   |-  >> void
|   |   |   |   BY (Reduce THEN Properties ['f(k+1)'] ...)
|   |   |   |      THEN (RepeatFunctionElim 5 ['x'] [] ...)
|   |   |   |      THEN (SetElementIntro ...)
|   |   |   6. x:Int
|   |   |   7. (1)(x)((k-1)+1)
|   |   |   8. (f(x)=k in int)->void
|   |   |   9. f(x)<1
|   |   |-  >> void
|   |   |   |   BY (Properties ['f(x)'] ...)
|   |   |   6. x:Int
|   |   |   7. (1)(x)((k-1)+1)
|   |   |   8. (f(x)=k in int)->void
|   |   |   9. k-1<f(x)
|   |   |-  >> void
|   |   |   |   BY (Properties ['f(x)'] ...)
|   |   |   6. i,j:{1..(((k-1))+1)} where i<j & 
|   |   |         (ˆx. if f(x)=k then f(k+1) else f(x))(i) 
|   |   |         = (ˆx. if f(x)=k then f(k+1) else f(x))(j)
|   |   |-  >> i,j:{1..(((k))+1)} where i<j & f(i)=f(j)
|   |   |   |   BY (ExplodeProduct 6 []  ...)
|   |   |   |      THEN (IntroTerms ['i';'j'] ...)
|   |   |   |   6. i:Int
|   |   |   |   7. (1)i((k-1)+1)
|   |   |   |   8. j:Int
|   |   |   |   9. (1)(j)((k-1)+1)
|   |   |   |   10. i<j & (ˆx. if f(x)=k then f(k+1) else f(x))(i) 
|   |   |   |             = (ˆx. if f(x)=k then f(k+1) else f(x))(j)
|   |   |   |-  >> f(i)=f(j)
|   |   |   |   |   BY (RepeatAndElim 10
|   |   |   |   |       THEN OnLastHyp ReduceHyp ...)
|   |   |   |   |   10. i<j
|   |   |   |   |   11. if f((i))=k then f(k+1) else f((i)) 
|   |   |   |   |       = if f((j))=k then f(k+1) else f((j)) in Int
|   |   |   |   |-  >> f(i)=f(j)
|   |   |   |   |   |   BY (let [a;b],() = 
|   |   |   |   |   |          destruct_equal (type_of_hyp 11 p) in
|   |   |   |   |   |       DecisionTermCases [ a,'Int'; b,'Int' ] ...)
|   |   |   |   |   |   12. f(i)=k in int
|   |   |   |   |   |   13. if f((i))=k then f(k+1) else f((i))=f(k+1) in Int
|   |   |   |   |   |   14. f(j)=k in int
|   |   |   |   |   |   15. if f((j))=k then f(k+1) else f((j))=f(j) in Int
|   |   |   |   |   |-  >> f(i)=f(j)
|   |   |   |   |   |   |   BY Reduce
|   |   |   |   |   |   |      THEN (ElimOn 5 'j' ...)
|   |   |   |   |   |   |      THEN (OnLastHyp Elim ...)
|   |   |   |   |   |   |      THEN (SetElementIntro ...)
|   |   |   |   |   |   |   5. x:{1..(k)}->((f(x)=f(k+1) in {1..(k)})->void)
|   |   |   |   |   |   |   16. (f(j)=f(k+1) in {1..(k)})->void
|   |   |   |   |   |   |   17. f(j)<1
|   |   |   |   |   |   |-  >> void
|   |   |   |   |   |   |   |   BY (Properties ['f(j)'] ...)
|   |   |   |   |   |   |   5. x:{1..(k)}->((f(x)=f(k+1) in {1..(k)})->void)
|   |   |   |   |   |   |   16. (f(j)=f(k+1) in {1..(k)})->void
|   |   |   |   |   |   |   17. k<f(j)
|   |   |   |   |   |   |-  >> void
|   |   |   |   |   |   |   |   BY (Properties ['f(j)'] ...)
|   |   |   |   |   |   12. f(i)=k in int
|   |   |   |   |   |   13. if f((i))=k then f(k+1) else f((i))=f(i) in Int
|   |   |   |   |   |   14. f(j)=k in int
|   |   |   |   |   |   15. if f((j))=k then f(k+1) else f((j))=f(k+1) in Int
|   |   |   |   |   |-  >> f(i)=f(j)
|   |   |   |   |   |   |   BY Reduce
|   |   |   |   |   |   |      THEN (ElimOn 5 'i' ...)
|   |   |   |   |   |   |      THEN (OnLastHyp Elim ...)
|   |   |   |   |   |   |      THEN (SetElementIntro ...)
|   |   |   |   |   |   |   5. x:{1..(k)}->((f(x)=f(k+1) in {1..(k)})->void)
|   |   |   |   |   |   |   16. (f(i)=f(k+1) in {1..(k)})->void
|   |   |   |   |   |   |   17. f(i)<1
|   |   |   |   |   |   |-  >> void
|   |   |   |   |   |   |   |   BY (Properties ['f(i)'] ...)
|   |   |   |   |   |   |   5. x:{1..(k)}->((f(x)=f(k+1) in {1..(k)})->void)
|   |   |   |   |   |   |   16. (f(i)=f(k+1) in {1..(k)})->void
|   |   |   |   |   |   |   17. k<f(i)
|   |   |   |   |   |   |-  >> void
|   |   |   |   |   |   |   |   BY (Properties ['f(i)'] ...)
