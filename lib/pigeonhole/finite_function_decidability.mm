>> m,n:N. f:{1..m}->{1..n}. y:{1..n}. 
          x:{1..m} where f(x)=y in {1..n}
         x:{1..m}. (f(x)=y in {1..n})
|   BY (InductionOn `m` `k` ...)
|   1. n:Int
|   2. 0n
|   3. f:{1..((0))}->{1..n}
|   4. y:Int
|   5. (1)(y)n
|-  >> x:{1..((0))} where f(x)=y in {1..n}
|            x:{1..((0))}. (f(x)=y in {1..n})
|   |   BY (IntroRight ...)
|   1. k:int
|   2. 0<k
|   3. n:N. f:{1..((k-1))}->{1..n}. y:{1..n}. 
|             x:{1..((k-1))} where f(x)=y in {1..n}
|            x:{1..((k-1))}. (f(x)=y in {1..n})
|   4. n:Int
|   5. 0n
|   6. f:{1..((k))}->{1..n}
|   7. y:Int
|   8. (1)(y)n
|-  >> x:{1..((k))} where f(x)=y in {1..n}
|            x:{1..((k))}. (f(x)=y in {1..n})
|   |   BY (Cases [ 'f(k)=y'; '(f(k)=y)' ] ...)
|   |   9. f(k)=y
|   |-  >> x:{1..((k))} where f(x)=y in {1..n}
|   |            x:{1..((k))}. (f(x)=y in {1..n})
|   |   |   BY (IntroLeft THENW IntroTerm 'k' ...)
|   |   |-  >> f(k)=y in {1..n}
|   |   |   |   BY (SetElementIntro ...)
|   |   9. (f(k)=y)
|   |-  >> x:{1..((k))} where f(x)=y in {1..n}
|   |            x:{1..((k))}. (f(x)=y in {1..n})
|   |   |   BY (InstantiateHyp 3 [ 'n'; 'ˆx.f(x)'; 'y' ] ...)
|   |   |   10. x:{1..((k-1))} where (ˆx.f(x))(x)=y in {1..n}
|   |   |            x:{1..((k-1))}. ((ˆx.f(x))(x)=y in {1..n})
|   |   |-  >> x:{1..((k))} where f(x)=y in {1..n}
|   |   |            x:{1..((k))}. (f(x)=y in {1..n})
|   |   |   |   BY ((CaseHyp 10 ...) THENL [IntroLeft; IntroRight] ...)
|   |   |   |   10. x:Int
|   |   |   |   11. (1)(x)(k-1)
|   |   |   |   12. (ˆx.f(x))(x)=y in {1..n}
|   |   |   |-  >> x:{1..((k))} where f(x)=y in {1..n}
|   |   |   |   |   BY (Reduce THEN IntroTerm 'x'  ...)
|   |   |   |   10. x:{1..((k-1))}. ((ˆx.f(x))(x)=y in {1..n})
|   |   |   |   11. x:Int
|   |   |   |   12. (1)(x)(k)
|   |   |   |   13. f(x)=y in {1..n}
|   |   |   |-  >> void
|   |   |   |   |   BY (Cases [ 'x=k'; 'x<k' ]  ...)
|   |   |   |   |   14. x=k
|   |   |   |   |-  >> void
|   |   |   |   |   |   BY (ElimEquality 13 ...)
|   |   |   |   |   14. x<k
|   |   |   |   |-  >> void
|   |   |   |   |   |   BY (Reduce THEN ElimOn 10 'x' THENM Contradiction ...)
