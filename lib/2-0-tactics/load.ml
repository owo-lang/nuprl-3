let tactics = ``init term-1 term-2 tactics-1 tactics-2 tactics-3 
                tactics-4 tactics-5 tactics-6 tactics-7 tactics-8 tactics-9 autotactic`` 
in
map (\x. load (complete_nuprl_path ``lib 2-0-tactics`` x) false) tactics
;; 









