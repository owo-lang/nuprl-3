>> m,n:N+. B:({0..(m-1)}->{0..(n-1)}->Int) where sorted(B{m,n}). x:Int.
      k:N. i:{0..(m-1)}. j:{0..(n-1)} where i+(n-j) = k.
        x  B{m,n}(0:i, j:(n-1))  (x  B{m,n}(0:i, j:(n-1)))
|   BY (InductionOn `k` `l` ...)
|   1. m:Int
|   2. 0<m
|   3. n:Int
|   4. 0<n
|   5. B:{0..(m-1)}->{0..(n-1)}->Int
|   6. x:Int
|   7. i:Int
|   8. (0)i(m-1)
|   9. j:Int
|   10. (0)(j)(n-1)
|   11. 0 in int
|   12. i+(n-j) = ((0))
|   13. 0 in int
|   14. sorted(B{m,n})
|-  >> x  B{m,n}(0:i, j:(n-1))  (x  B{m,n}(0:i, j:(n-1)))
|   |   BY (OnEveryHyp RepeatAndElim ...)
|   |   8. j:Int
|   |   9. 0 in int
|   |   10. i+(n-j) = ((0))
|   |   12. sorted(B{m,n})
|   |   13. (0)(j)
|   |   14. (j)(n-1)
|   |   15. (0)i
|   |   16. i(m-1)
|   |-  >> x  B{m,n}(0:i, j:(n-1))  (x  B{m,n}(0:i, j:(n-1)))
|   |   |   BY (ref `monotonicity 10+14` 
|   |   |       THEN BothSidesBy 15 `+` 'n' ...)
|   1. m:Int
|   2. 0<m
|   3. n:Int
|   4. 0<n
|   5. B:{0..(m-1)}->{0..(n-1)}->Int
|   6. x:Int
|   7. l:int
|   8. 0<l
|   9. i:{0..(m-1)}. j:{0..(n-1)} where i+(n-j) = ((l-1)).
|           x  B{m,n}(0:i, j:(n-1))  (x  B{m,n}(0:i, j:(n-1)))
|   10. i:Int
|   11. (0)i(m-1)
|   12. j:Int
|   13. (0)(j)(n-1)
|   14. 0 in int
|   15. i+(n-j) = ((l))
|   16. 0 in int
|   17. sorted(B{m,n})
|-  >> x  B{m,n}(0:i, j:(n-1))  (x  B{m,n}(0:i, j:(n-1)))
|   |   BY (Thinning [14;16] 
|   |      THEN Cases [ 'B(i,j)<x'; 'B(i,j)=x'; 'x<B(i,j)']
|   |       ...)
|   |   14. i+(n-j) = ((l))
|   |   15. sorted(B{m,n})
|   |   16. B(i,j)<x
|   |-  >> x  B{m,n}(0:i, j:(n-1))  (x  B{m,n}(0:i, j:(n-1)))
|   |   |   BY (Cases ['j<n-1'; 'j=n-1'] ...)
|   |   |   17. j<n-1
|   |   |-  >> x  B{m,n}(0:i, j:(n-1))  (x  B{m,n}(0:i, j:(n-1)))
|   |   |   |   BY (InstantiateHyp 9 ['i'; 'j+1'] ...)
|   |   |   |   18. x  B{m,n}(0:i, (j+1):(n-1))  (x  B{m,n}(0:i, (j+1):(n-1)))
|   |   |   |-  >> x  B{m,n}(0:i, j:(n-1))  (x  B{m,n}(0:i, j:(n-1)))
|   |   |   |   |   BY (CaseHyp 18 
|   |   |   |   |       THENL [IntroLeft; IntroRight] ...)
|   |   |   |   |   18. x  B{m,n}(0:i, (j+1):(n-1))
|   |   |   |   |-  >> x  B{m,n}(0:i, j:(n-1))
|   |   |   |   |   |   BY (ExplodeProduct 18 [`r`;`s`]  ...)
|   |   |   |   |   |      THEN (IntroTerms ['r';'s'] ...)
|   |   |   |   |   18. (x  B{m,n}(0:i, (j+1):(n-1)))
|   |   |   |   |   19. x  B{m,n}(0:i, j:(n-1))
|   |   |   |   |-  >> void
|   |   |   |   |   |   BY (ExplodeProduct 19 [`r`;`s`] ...)
|   |   |   |   |   |       THEN (Cases ['s=j'; 'j<s'] ...)
|   |   |   |   |   |   19. r:Int
|   |   |   |   |   |   20. (0)(r)(m-1)
|   |   |   |   |   |   21. s:Int
|   |   |   |   |   |   22. (0)(s)(n-1)
|   |   |   |   |   |   23. B(r,s) = x & (0)  r  (i) & j  s  (n-1)
|   |   |   |   |   |   24. s=j
|   |   |   |   |   |-  >> void
|   |   |   |   |   |   |   BY (ColSorted 15 'j' 'r' 'i' ...)
|   |   |   |   |   |   19. r:Int
|   |   |   |   |   |   20. (0)(r)(m-1)
|   |   |   |   |   |   21. s:Int
|   |   |   |   |   |   22. (0)(s)(n-1)
|   |   |   |   |   |   23. B(r,s) = x & (0)  r  (i) & j  s  (n-1)
|   |   |   |   |   |   24. j<s
|   |   |   |   |   |-  >> void
|   |   |   |   |   |   |   BY (Elim 18 ...)
|   |   |   |   |   |   |      THEN (IntroTerms ['r';'s'] ...)
|   |   |   17. j=n-1
|   |   |-  >> x  B{m,n}(0:i, j:(n-1))  (x  B{m,n}(0:i, j:(n-1)))
|   |   |   |   BY (IntroRight ...)
|   |   |   |      THEN (ExplodeProduct 18 [`r`; `s`] ...)
|   |   |   |   18. r:Int
|   |   |   |   19. (0)(r)(m-1)
|   |   |   |   20. s:Int
|   |   |   |   21. (0)(s)(n-1)
|   |   |   |   22. B(r,s) = x & (0)  r  (i) & j  s  (n-1)
|   |   |   |-  >> void
|   |   |   |   |   BY (ColSorted 15 'j' 'r' 'i' ...)
|   |   14. i+(n-j) = ((l))
|   |   15. sorted(B{m,n})
|   |   16. B(i,j)=x
|   |-  >> x  B{m,n}(0:i, j:(n-1))  (x  B{m,n}(0:i, j:(n-1)))
|   |   |   BY (IntroLeft THENW IntroTerms ['i'; 'j'] ...)
|   |   14. i+(n-j) = ((l))
|   |   15. sorted(B{m,n})
|   |   16. x<B(i,j)
|   |-  >> x  B{m,n}(0:i, j:(n-1))  (x  B{m,n}(0:i, j:(n-1)))
|   |   |   BY % This branch of the proof is analogous to the B(i,j)<x branch, and
|   |   |        was proved using that branch as a guide.  Some of the proof
|   |   |        steps have been combined, giving a less readable result. 
|   |   |      %
|   |   |      (Cases ['0<i'; 'i=0'] ...)
|   |   |   17. 0<i
|   |   |-  >> x  B{m,n}(0:i, j:(n-1))  (x  B{m,n}(0:i, j:(n-1)))
|   |   |   |   BY (InstantiateHyp 9 ['i-1'; 'j'] ...)
|   |   |   |   18. x  B{m,n}(0:(i-1), j:(n-1))  (x  B{m,n}(0:(i-1), j:(n-1)))
|   |   |   |-  >> x  B{m,n}(0:i, j:(n-1))  (x  B{m,n}(0:i, j:(n-1)))
|   |   |   |   |   BY (CaseHyp 18 
|   |   |   |   |       THENL [IntroLeft; IntroRight] ...)
|   |   |   |   |      THENL
|   |   |   |   |        [(ExplodeProduct 18 [`r`;`s`]  ...)
|   |   |   |   |         THEN (IntroTerms ['r';'s'] ...)
|   |   |   |   |        ;(ExplodeProduct 19 [`r`;`s`] ...)
|   |   |   |   |         THEN (Cases ['r=i'; 'r<i'] ...)
|   |   |   |   |        ]
|   |   |   |   |      
|   |   |   |   |   18. (x  B{m,n}(0:(i-1), j:(n-1)))
|   |   |   |   |   19. r:Int
|   |   |   |   |   20. (0)(r)(m-1)
|   |   |   |   |   21. s:Int
|   |   |   |   |   22. (0)(s)(n-1)
|   |   |   |   |   23. B(r,s) = x & (0)  r  (i) & j  s  (n-1)
|   |   |   |   |   24. r=i
|   |   |   |   |-  >> void
|   |   |   |   |   |   BY (RowSorted 15 'i' 'j' 's' ...)
|   |   |   |   |   18. (x  B{m,n}(0:(i-1), j:(n-1)))
|   |   |   |   |   19. r:Int
|   |   |   |   |   20. (0)(r)(m-1)
|   |   |   |   |   21. s:Int
|   |   |   |   |   22. (0)(s)(n-1)
|   |   |   |   |   23. B(r,s) = x & (0)  r  (i) & j  s  (n-1)
|   |   |   |   |   24. r<i
|   |   |   |   |-  >> void
|   |   |   |   |   |   BY (Elim 18 ...)
|   |   |   |   |   |      THEN (IntroTerms ['r';'s'] ...)
|   |   |   17. i=0
|   |   |-  >> x  B{m,n}(0:i, j:(n-1))  (x  B{m,n}(0:i, j:(n-1)))
|   |   |   |   BY (IntroRight ...)
|   |   |   |      THEN (ExplodeProduct 18 [`r`; `s`] ...)
|   |   |   |      THEN (RowSorted 15 'i' 'j' 's' ...)
