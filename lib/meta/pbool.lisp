(PRL-LIB-DUMP(|BEGIN_PBool| DEF(TTREE 61 61))(|Bool_| THM((TTREE 62 62 32 85 49 0)((
TTREE(|wf|(TTREE 69 120 112 108 105 99 105 116 73 32 39(|or|(TTREE(|True|))(TTREE(
|True|)))39 32)))NIL)(TTREE(|or|(TTREE(|True|))(TTREE(|True|)))))()COMPLETE)(|Bool| DEF(TTREE 66 111
111 108 61 61(|e|(TTREE 66 111 111 108))))(|btrue_| THM((TTREE 62 62 32(|Bool|)0)((TTREE(
|wf|(TTREE 69 120 112 108 105 99 105 116 73 32 39 105 110 108 40(|ax|)41 39 32))
0)NIL)(TTREE 105 110 108 40(|ax|)41))()COMPLETE)(|btrue| DEF(TTREE 116 114 117 101 61 
61(|e|(TTREE 98 116 114 117 101))))(|is_btrue_| THM((TTREE 62 62 32(|Bool|)32 45 62 32
85 49 0)((TTREE(|wf|(TTREE 69 120 112 108 105 99 105 116 73 32 39(|l|(TTREE 98)(
TTREE(|isl|(TTREE 98))))39 32))0)NIL)(TTREE(|l|(TTREE 98)(TTREE(|isl|(TTREE 98))))))()COMPLETE)(
|is_btrue| DEF(TTREE 60 98 58 66 111 111 108 62 61 61(|ap|(TTREE(|e|(TTREE 105 
115 95 98 116 114 117 101)))(TTREE 60 98 62))))(|bfalse_| THM((TTREE 62 62 32(|Bool|)0)((
TTREE(|wf|(TTREE 69 120 112 108 105 99 105 116 73 32 39 105 110 114 40(|ax|)41
39 32))0)NIL)(TTREE 105 110 114 40(|ax|)41))()COMPLETE)(|bfalse| DEF(TTREE 102 97 108 115
101 61 61(|e|(TTREE 98 102 97 108 115 101))))(|is_bfalse_| THM((TTREE 62 62 32(|Bool|)
32 45 62 32 85 49 0 0)((TTREE(|wf|(TTREE 69 120 112 108 105 99 105 116 73 32 39(
|l|(TTREE 98)(TTREE(|isr|(TTREE 98))))39 32))0 0)NIL)(TTREE(|l|(TTREE 98)(TTREE(|isr|(TTREE 98))))))()
COMPLETE)(|is_bfalse| DEF(TTREE 147 40 60 98 58 66 111 111 108 62 41 61 61(|ap|(
TTREE(|e|(TTREE 105 115 95 98 102 97 108 115 101)))(TTREE 60 98 62))))(|bif_| THM((TTREE
62 62 32 79 98 106 101 99 116 0)((TTREE(|wf|(TTREE 69 120 112 108 105 99 105 116
73 32 39(|l3|(TTREE 98)(TTREE 102)(TTREE 103)(TTREE(|dec|(TTREE 98)(TTREE 117)(TTREE 102
40 117 41)(TTREE 118)(TTREE 103 40 118 41))))39 32))0)NIL)(TTREE(|l3|(TTREE 98)(TTREE 102)(
TTREE 103)(TTREE(|dec|(TTREE 98)(TTREE 117)(TTREE 102 40 117 41)(TTREE 118)(TTREE 103 
40 118 41))))))()COMPLETE)(|bif| DEF(TTREE 105 102 32 60 98 58 66 111 111 108 62 32 
116 104 101 110 32 60 102 58 84 114 117 101 45 92 62 42 62 32 101 108 115 
101 32 60 103 58 84 114 117 101 45 92 62 42 62 61 61(|ap|(TTREE(|ap|(TTREE(|ap|(
TTREE(|e|(TTREE 98 105 102)))(TTREE 60 98 62)))(TTREE 60 102 62)))(TTREE 60 103 62))))(|bif__|
THM((TTREE 62 62 32(|all|(TTREE 65)(TTREE(|Type|))(TTREE(|all|(TTREE 98)(TTREE(|Bool|))(TTREE(
|all|(TTREE 102)(TTREE(|squash|(TTREE(|is_btrue|(TTREE 98))))45 62 65)(TTREE(|all|(TTREE 
103)(TTREE(|squash|(TTREE(|is_bfalse|(TTREE 98))))45 62 65)(TTREE 0 32 32 40(|bif|(TTREE
98)(TTREE 102)(TTREE 103))41 32 105 110 32 65)))))))))((TTREE(|wf|(TTREE 85 110 102 111 108 
100 32 96 98 105 102 96 32 84 72 69 78 32 79 110 86 97 114 32 96 98 96 32 
69 32))0 84 72 69 78 32(|wf|(TTREE 69 118 97 108 67 111 110 99 108 32)))NIL)(TTREE 
92 65 46 92 98 46 100 101 99 105 100 101 40 98 59 97 51 46 92 102 46 92 103
46 97 120 105 111 109 59 98 52 46 92 102 46 92 103 46 97 120 105 111 109 41))()
COMPLETE)(|PBool_| THM((TTREE 62 62 32(|Topp|)0)((TTREE(|wf|(TTREE 69 120 112 108 105
99 105 116 73 32 39(|or|(TTREE(|Bool|))(TTREE(|Top|)))39 32))0)NIL)(TTREE(|or|(TTREE(|Bool|))(
TTREE(|Top|)))))()COMPLETE)(|PBool| DEF(TTREE 80 66 111 111 108 61 61(|e|(TTREE 80 66 
111 111 108))))(|PBoolE| ML(TTREE 115 101 116 95 100 95 116 97 99 116 105 99 95 
97 114 103 115 32 49 32 91 93 32 91 93 32 91 93 32 59 59 32 0 0 108 101 116
32 80 66 111 111 108 69 32 105 32 61 0 32 80 97 116 116 101 114 110 32 96 
80 66 111 111 108 69 95 112 97 116 116 101 114 110 96 32 91 93 32 91 93 32
91 93 32 105 32 59 59 32 0 0))(|PBoolE_pattern| THM((TTREE 62 62 32 120 58(
|PBool|)32 45 62 32 34 80 34 40 120 41 0)((TTREE 73 0)(((TTREE(F(TTREE 69 32 40 104 
121 112 95 110 117 109 95 97 114 103 40 41 41)))(((TTREE 84 104 105 110 32 40 104
121 112 95 110 117 109 95 97 114 103 40 41 41 32 84 72 69 78 32(F(TTREE 79 
110 76 97 115 116 72 121 112 32 40 92 105 46 32 69 32 105 32 84 72 69 78 32
84 104 105 110 32 105 41))0)(((TTREE 0)())((TTREE 0)())))((TTREE 84 104 105 110 32 40 104 121 
112 95 110 117 109 95 97 114 103 40 41 41 0)(((TTREE 0)())))))((TTREE 0)()))))()PARTIAL)(|prop_| THM((
TTREE 62 62 32 79 98 106 101 99 116)((TTREE(|wf|(TTREE 69 120 112 108 105 99 105
116 73 32 39(|l|(TTREE 80)(TTREE 105 110 114 40 80 41))39 32))0)NIL)(TTREE(|l|(TTREE 80)(
TTREE 105 110 114 40 80 41))))()COMPLETE)(|prop| DEF(TTREE 112 114 111 112 40 60 80
58 85 62 41 61 61(|ap|(TTREE(|e|(TTREE 112 114 111 112)))(TTREE 60 80 62))))(|prop__| 
THM((TTREE 62 62 32(|all|(TTREE 81)(TTREE(|Top|))(TTREE(|prop|(TTREE 81))32 105 110 32(
|PBool|)))0)((TTREE(|wf|(TTREE 85 110 102 111 108 100 32 96 112 114 111 112 96 32))0)
NIL)(TTREE 92 81 46 97 120 105 111 109))()COMPLETE)(|bool_| THM((TTREE 62 62 32 79 98
106 101 99 116)((TTREE(|wf|(TTREE 69 120 112 108 105 99 105 116 73 32 39(|l|(TTREE
98)(TTREE 105 110 108 40 98 41))39 32))0)NIL)(TTREE(|l|(TTREE 98)(TTREE 105 110 108 40 
98 41))))()COMPLETE)(|bool| DEF(TTREE 98 111 111 108 40 60 80 58 66 111 111 108 62 
41 61 61(|ap|(TTREE(|e|(TTREE 98 111 111 108)))(TTREE 60 80 62))))(|bool__| THM((TTREE 62
62 32(|all|(TTREE 98)(TTREE(|Bool|))(TTREE(|bool|(TTREE 98))32 105 110 32(|PBool|)))0)((TTREE(
|wf|(TTREE 85 110 102 111 108 100 32 96 98 111 111 108 96 32))0)NIL)(TTREE 92 98
46 97 120 105 111 109))()COMPLETE)(|PBool_cases_| THM((TTREE 62 62 32 79 98 106 101
99 116)((TTREE(|wf|(TTREE 69 120 112 108 105 99 105 116 73 32 39(|l3|(TTREE 116 
116)(TTREE 102 102)(TTREE 103)(TTREE(|l|(TTREE 116)(TTREE(|dec|(TTREE 116)(TTREE 117)(TTREE(
|dec|(TTREE 117)(TTREE 118)(TTREE 116 116)(TTREE 118)(TTREE 102 102)))(TTREE 117)(TTREE 
103 40 117 41))))))39 32))0)NIL)(TTREE(|l3|(TTREE 116 116)(TTREE 102 102)(TTREE 103)(TTREE(|l|(
TTREE 116)(TTREE(|dec|(TTREE 116)(TTREE 117)(TTREE(|dec|(TTREE 117)(TTREE 118)(TTREE 116
116)(TTREE 118)(TTREE 102 102)))(TTREE 117)(TTREE 103 40 117 41))))))))()COMPLETE)(|PBool_cases|
DEF(TTREE 99 97 115 101 32 60 112 98 58 80 66 111 111 108 40 80 41 62 32 32
32 116 114 117 101 58 32 60 116 116 58 65 62 32 102 97 108 115 101 58 32 60
102 102 58 65 62 32 101 108 115 101 58 32 60 103 58 85 45 92 62 65 62 61 61(
|nothing|(TTREE 0))(|ap|(TTREE(|ap|(TTREE(|ap|(TTREE(|ap|(TTREE(|e|(TTREE 80 66 111 111
108 95 99 97 115 101 115)))(TTREE 60 116 116 62)))(TTREE 60 102 102 62)))(TTREE 60 103
62)))(TTREE 60 112 98 62))))(|PBool_cases__| THM((TTREE 62 62 32(|all|(TTREE 65)(TTREE(
|Type|))(TTREE(|all2|(TTREE 116 116)(TTREE 102 102)(TTREE 65)(TTREE(|all|(TTREE 103)(TTREE(
|Top|)45 62 65)(TTREE(|all|(TTREE 112 98)(TTREE(|PBool|))(TTREE 0 32 32(|PBool_cases|(
TTREE 112 98)(TTREE 116 116)(TTREE 102 102)(TTREE 103))32 105 110 32 65))))))))0)((TTREE(|wf|(
TTREE 85 110 102 111 108 100 32 96 80 66 111 111 108 95 99 97 115 101 115 
96 32))0)NIL)(TTREE 92 65 46 92 116 116 46 92 102 102 46 92 103 46 92 112 98 46
97 120 105 111 109))()COMPLETE)(|is_pbtrue_| THM((TTREE 62 62 32(|PBool|)32 45 62 32(
|Top|))((TTREE 69 120 112 108 105 99 105 116 73 32 0 39(|l|(TTREE 112 98)(TTREE(
|PBool_cases|(TTREE 112 98)(TTREE(|True|))(TTREE(|False|))(TTREE(|l|(TTREE 81)(TTREE 81))))))39
0 0)(((TTREE(|wf|(TTREE 84 121 112 101 83 117 98 116 101 114 109 32 39(|False|)39 
32 39(|Top|)39 32))0)NIL)))(TTREE(|l|(TTREE 112 98)(TTREE(|PBool_cases|(TTREE 112 98)(TTREE(
|True|))(TTREE(|False|))(TTREE(|l|(TTREE 81)(TTREE 81))))))))()COMPLETE)(|is_pbtrue| DEF(TTREE 60 
112 98 58 80 66 111 111 108 62 61 61(|ap|(TTREE(|e|(TTREE 105 115 95 112 98 116
114 117 101)))(TTREE 60 112 98 62))))(|prop_char| THM((TTREE 62 62 32(|all|(TTREE 81)(
TTREE(|Top|))(TTREE(|iff|(TTREE(|is_pbtrue|(TTREE(|prop|(TTREE 81)))))(TTREE 81))))0)((TTREE(|wf|(
TTREE 82 101 112 101 97 116 32 73 32 84 72 69 78 87 32 69 118 97 108 32))0)NIL)(
TTREE 92 81 46 40 92 118 48 46 40 92 118 49 46 60 118 48 44 118 49 62 41 40
92 118 51 46 118 51 41 41 40 92 118 50 46 118 50 41))()COMPLETE)(|pband_| THM((
TTREE 62 62 32(|PBool|)32 45 62 32(|PBool|)32 45 62 32(|PBool|))((TTREE 69 120 112 
108 105 99 105 116 73 32 0 39(|l2|(TTREE 112 98 49)(TTREE 112 98 50)(TTREE 0(
|PBool_cases|(TTREE 112 98 49 0)(TTREE 112 98 50 0 32 32)(TTREE(|bool|(TTREE(
|bfalse|)))0 32 32)(TTREE(|l|(TTREE 81 49)(TTREE(|PBool_cases|(TTREE 112 98 50)(TTREE(
|prop|(TTREE 81 49)))(TTREE(|bool|(TTREE(|bfalse|))))(TTREE(|l|(TTREE 81 50)(TTREE(|prop|(
TTREE(|and|(TTREE 81 49)(TTREE 81 50))))))))))))))39 32 0 0)(((TTREE(|wf|(TTREE 73 100 32)))NIL)))(TTREE(
|l2|(TTREE 112 98 49)(TTREE 112 98 50)(TTREE 0(|PBool_cases|(TTREE 112 98 49 0)(
TTREE 112 98 50 0 32 32)(TTREE(|bool|(TTREE(|bfalse|)))0 32 32)(TTREE(|l|(TTREE 81 49)(
TTREE(|PBool_cases|(TTREE 112 98 50)(TTREE(|prop|(TTREE 81 49)))(TTREE(|bool|(TTREE(
|bfalse|))))(TTREE(|l|(TTREE 81 50)(TTREE(|prop|(TTREE(|and|(TTREE 81 49)(TTREE 81 50))))))))))))))))()
COMPLETE)(|pband| DEF(TTREE 60 80 58 80 66 111 111 108 62 32 38 32 60 81 58 80
66 111 111 108 62 61 61(|ap|(TTREE(|ap|(TTREE(|e|(TTREE 112 98 97 110 100)))(TTREE 60
80 62)))(TTREE 60 81 62))))(|pband_char| THM((TTREE 62 62 32(|all2|(TTREE 112 98 49)(TTREE
112 98 50)(TTREE(|PBool|))(TTREE(|iff|(TTREE(|is_pbtrue|(TTREE(|pband|(TTREE 112 98 49)(
TTREE 112 98 50)))))(TTREE(|and|(TTREE(|is_pbtrue|(TTREE 112 98 49)))(TTREE(|is_pbtrue|(
TTREE 112 98 50))))))))0)((TTREE(|wf|(TTREE 79 110 86 97 114 32 96 112 98 49 96 32 80 66
111 111 108 69 32 84 72 69 78 87 32 79 110 86 97 114 32 96 112 98 50 96 32
80 66 111 111 108 69 32 84 72 69 78 87 32 69 118 97 108 67 111 110 99 108 
32))0)NIL)(TTREE 92 112 98 49 46 100 101 99 105 100 101 40 112 98 49 59 97 49 46
100 101 99 105 100 101 40 97 49 59 97 50 46 92 112 98 50 46 100 101 99 105
100 101 40 112 98 50 59 97 51 46 100 101 99 105 100 101 40 97 51 59 97 52 
46 40 92 118 48 46 40 92 118 49 46 60 118 48 44 118 49 62 41 40 92 118 53 
46 97 50 41 41 40 92 118 50 46 40 92 118 51 46 40 92 118 52 46 60 97 50 44
97 50 62 41 40 97 50 41 41 40 97 50 41 41 59 98 53 46 40 92 118 54 46 40 92
118 55 46 60 118 54 44 118 55 62 41 40 92 118 57 46 115 112 114 101 97 100
40 118 57 59 118 49 48 44 118 49 49 46 97 110 121 40 118 49 49 41 41 41 41
40 92 118 56 46 97 110 121 40 118 56 41 41 41 59 98 52 46 40 92 118 49 50 
46 40 92 118 49 51 46 60 118 49 50 44 118 49 51 62 41 40 92 118 49 55 46 
115 112 114 101 97 100 40 118 49 55 59 118 49 56 44 118 49 57 46 118 49 57
41 41 41 40 92 118 49 52 46 40 92 118 49 53 46 40 92 118 49 54 46 60 97 50
44 118 49 52 62 41 40 118 49 52 41 41 40 97 50 41 41 41 59 98 51 46 92 112
98 50 46 100 101 99 105 100 101 40 112 98 50 59 97 52 46 100 101 99 105 100
101 40 97 52 59 97 53 46 40 92 118 50 48 46 40 92 118 50 49 46 60 118 50 48
44 118 50 49 62 41 40 92 118 50 51 46 115 112 114 101 97 100 40 118 50 51 
59 118 50 52 44 118 50 53 46 97 110 121 40 118 50 52 41 41 41 41 40 92 118
50 50 46 97 110 121 40 118 50 50 41 41 59 98 54 46 40 92 118 50 54 46 40 92
118 50 55 46 60 118 50 54 44 118 50 55 62 41 40 92 118 50 57 46 115 112 114
101 97 100 40 118 50 57 59 118 51 48 44 118 51 49 46 97 110 121 40 118 51 
48 41 41 41 41 40 92 118 50 56 46 97 110 121 40 118 50 56 41 41 41 59 98 53
46 40 92 118 51 50 46 40 92 118 51 51 46 60 118 51 50 44 118 51 51 62 41 40
92 118 51 53 46 115 112 114 101 97 100 40 118 51 53 59 118 51 54 44 118 51
55 46 97 110 121 40 118 51 54 41 41 41 41 40 92 118 51 52 46 97 110 121 40
118 51 52 41 41 41 41 59 98 50 46 92 112 98 50 46 100 101 99 105 100 101 40
112 98 50 59 97 51 46 100 101 99 105 100 101 40 97 51 59 97 52 46 40 92 118
51 56 46 40 92 118 51 57 46 60 118 51 56 44 118 51 57 62 41 40 92 118 52 51
46 115 112 114 101 97 100 40 118 52 51 59 118 52 52 44 118 52 53 46 118 52
52 41 41 41 40 92 118 52 48 46 40 92 118 52 49 46 40 92 118 52 50 46 60 118
52 48 44 97 52 62 41 40 97 52 41 41 40 118 52 48 41 41 59 98 53 46 40 92 
118 52 54 46 40 92 118 52 55 46 60 118 52 54 44 118 52 55 62 41 40 92 118 
52 57 46 115 112 114 101 97 100 40 118 52 57 59 118 53 48 44 118 53 49 46 
97 110 121 40 118 53 49 41 41 41 41 40 92 118 52 56 46 97 110 121 40 118 52
56 41 41 41 59 98 52 46 40 92 118 53 50 46 40 92 118 53 51 46 60 118 53 50
44 118 53 50 62 41 40 118 53 50 41 41 40 92 118 53 52 46 118 53 52 41 41 41))()
COMPLETE)(|pbcand_| THM((TTREE 62 62 32 112 98 58(|PBool|)32 45 62 32 40(|squash|(
TTREE(|is_pbtrue|(TTREE 112 98))))45 62(|PBool|)41 32 45 62 32(|PBool|))((TTREE 69 120 
112 108 105 99 105 116 73 32 0 39(|l2|(TTREE 112 98 49)(TTREE 112 98 50)(TTREE 0(
|PBool_cases|(TTREE 112 98 49 0)(TTREE 112 98 50 40(|ax|)41 0 32 32)(TTREE(|bool|(
TTREE(|bfalse|)))0 32 32)(TTREE(|l|(TTREE 81 49)(TTREE(|prop|(TTREE(|and|(TTREE 81 49)(
TTREE(|is_pbtrue|(TTREE 112 98 50 40(|ax|)41))))))))))))39 32 0 0)(((TTREE(F(TTREE(|ww|(TTREE 77 
101 109 98 101 114 73 32 84 72 69 78 87 32 0 32 40 79 110 86 97 114 32 96 
112 98 49 96 32 80 66 111 111 108 69 32 84 72 69 78 32 69 118 97 108 67 111
110 99 108 32 84 72 69 78 32 77 101 109 98 101 114 73 32 84 72 69 78 87 32
69 118 97 108 67 111 110 99 108 41 32)))))(((TTREE(|wf|(TTREE 73 100 32))0)NIL)((TTREE(|wf|(
TTREE 73 100 32))0)NIL)((TTREE(|wf|(TTREE 84 121 112 101 83 117 98 116 101 114 109
32 39(|True|)39 32 39(|Top|)39 32))0)NIL)))))(TTREE(|l2|(TTREE 112 98 49)(TTREE 112 98 50)(
TTREE 0(|PBool_cases|(TTREE 112 98 49 0)(TTREE 112 98 50 40(|ax|)41 0 32 32)(TTREE(
|bool|(TTREE(|bfalse|)))0 32 32)(TTREE(|l|(TTREE 81 49)(TTREE(|prop|(TTREE(|and|(TTREE 81
49)(TTREE(|is_pbtrue|(TTREE 112 98 50 40(|ax|)41))))))))))))))()COMPLETE)(|pbcand| DEF(TTREE 60 80 
58 80 66 111 111 108 62 32 38 32 60 81 58 143 40 46 41 45 92 62 80 66 111 
111 108 62 61 61(|ap|(TTREE(|ap|(TTREE(|e|(TTREE 112 98 99 97 110 100)))(TTREE 60 80
62)))(TTREE 60 81 62))))(|pbcand_char| THM((TTREE 62 62 32(|all|(TTREE 112 98 49)(TTREE(
|PBool|))(TTREE(|all|(TTREE 112 98 50)(TTREE(|squash|(TTREE(|is_pbtrue|(TTREE 112 98 
49))))45 62(|PBool|))(TTREE 0 32 32(|iff|(TTREE(|is_pbtrue|(TTREE(|pbcand|(TTREE 112 98 
49)(TTREE 112 98 50)))))(TTREE(|and|(TTREE(|is_pbtrue|(TTREE 112 98 49)))(TTREE(|is_pbtrue|(
TTREE 112 98 50 40(|ax|)41)))))))))))((TTREE(|wf|(TTREE 79 110 86 97 114 32 96 112 98 49 96
32 80 66 111 111 108 69 32))32 0 84 72 69 78 32(|wf|(TTREE 69 118 97 108 69 120
99 101 112 116 32 40 100 101 102 115 32 96 80 66 111 111 108 96 41 32)))NIL)(
TTREE 92 112 98 49 46 100 101 99 105 100 101 40 112 98 49 59 97 49 46 100 
101 99 105 100 101 40 97 49 59 97 50 46 92 112 98 50 46 40 92 118 48 46 40
92 118 49 46 60 118 48 44 118 49 62 41 40 92 118 53 46 115 112 114 101 97 
100 40 118 53 59 118 54 44 118 55 46 118 55 41 41 41 40 92 118 50 46 40 92
118 51 46 40 92 118 52 46 60 118 51 44 118 52 62 41 40 118 50 41 41 40 97 
50 41 41 59 98 51 46 92 112 98 50 46 40 92 118 56 46 40 92 118 57 46 60 118
56 44 118 57 62 41 40 92 118 49 51 46 115 112 114 101 97 100 40 118 49 51 
59 118 49 52 44 118 49 53 46 97 110 121 40 118 49 52 41 41 41 41 40 92 118
49 48 46 40 92 118 49 49 46 40 92 118 49 50 46 60 118 49 49 44 118 49 50 62
41 40 97 110 121 40 118 49 48 41 41 41 40 97 110 121 40 118 49 48 41 41 41
41 59 98 50 46 92 112 98 50 46 40 92 118 49 54 46 40 92 118 49 55 46 60 118
49 54 44 118 49 55 62 41 40 92 118 50 53 46 115 112 114 101 97 100 40 118 
50 53 59 118 50 54 44 118 50 55 46 40 92 118 50 56 46 40 92 118 50 57 46 60
118 50 54 44 118 50 55 62 41 40 118 50 55 41 41 40 118 50 54 41 41 41 41 40
92 118 49 56 46 40 92 118 49 57 46 40 92 118 50 48 46 60 118 49 57 44 118 
50 48 62 41 40 115 112 114 101 97 100 40 118 49 56 59 118 50 51 44 118 50 
52 46 118 50 52 41 41 41 40 115 112 114 101 97 100 40 118 49 56 59 118 50 
49 44 118 50 50 46 118 50 49 41 41 41 41))()COMPLETE)(|pbnot_| THM((TTREE 62 62 32(
|PBool|)32 45 62 32(|PBool|))((TTREE 69 120 112 108 105 99 105 116 73 32 0 39(|l|(
TTREE 112 98)(TTREE 0(|PBool_cases|(TTREE 112 98)(TTREE(|bool|(TTREE(|bfalse|))))(TTREE(
|bool|(TTREE(|btrue|))))(TTREE(|l|(TTREE 81)(TTREE(|prop|(TTREE(|not|(TTREE 81))))))))))39 32 0 0)(((
TTREE(|wf|(TTREE 77 101 109 98 101 114 73 32 84 72 69 78 87 32 79 110 86 97 
114 32 96 112 98 96 32 80 66 111 111 108 69 32 84 72 69 78 87 32 69 118 97
108 67 111 110 99 108 32))0)NIL)))(TTREE(|l|(TTREE 112 98)(TTREE 0(|PBool_cases|(TTREE 
112 98)(TTREE(|bool|(TTREE(|bfalse|))))(TTREE(|bool|(TTREE(|btrue|))))(TTREE(|l|(TTREE 81)(TTREE(
|prop|(TTREE(|not|(TTREE 81))))))))))))()COMPLETE)(|pbnot| DEF(TTREE 147 40 60 112 98 58 80 66
111 111 108 62 41 61 61(|ap|(TTREE(|e|(TTREE 112 98 110 111 116)))(TTREE 60 112 98
62))))(|pbnot_char| THM((TTREE 62 62 32(|all|(TTREE 112 98)(TTREE(|PBool|))(TTREE(|iff|(
TTREE(|is_pbtrue|(TTREE(|pbnot|(TTREE 112 98)))))(TTREE(|not|(TTREE(|is_pbtrue|(TTREE 112
98))))))))0)((TTREE(|wf|(TTREE 79 110 86 97 114 32 96 112 98 96 32 80 66 111 111 108 69
32 84 72 69 78 87 32 69 118 97 108 67 111 110 99 108 32 84 72 69 78 32 66 
97 99 107 99 104 97 105 110 32))0)NIL)(TTREE 92 112 98 46 100 101 99 105 100 101
40 112 98 59 97 49 46 100 101 99 105 100 101 40 97 49 59 97 50 46 40 92 118
48 46 40 92 118 49 46 60 118 48 44 118 49 62 41 40 92 118 53 46 40 92 118 
54 46 40 92 118 55 46 118 55 41 40 118 54 40 97 50 41 41 41 40 118 53 41 41
41 40 92 118 50 46 92 118 51 46 40 92 118 52 46 97 110 121 40 118 50 41 41
40 97 110 121 40 118 50 41 41 41 59 98 51 46 40 92 118 56 46 40 92 118 57 
46 60 118 56 44 118 57 62 41 40 92 118 49 51 46 40 92 118 49 52 46 98 51 41
40 98 51 41 41 41 40 92 118 49 48 46 92 118 49 49 46 40 92 118 49 50 46 97
110 121 40 118 49 49 41 41 40 97 110 121 40 118 49 49 41 41 41 41 59 98 50
46 40 92 118 49 53 46 40 92 118 49 54 46 60 118 49 53 44 118 49 53 62 41 40
92 118 50 49 46 92 118 50 50 46 40 92 118 50 51 46 40 92 118 50 52 46 118 
50 52 41 40 118 50 51 40 118 50 50 41 41 41 40 118 50 49 41 41 41 40 92 118
49 55 46 92 118 49 56 46 40 92 118 49 57 46 40 92 118 50 48 46 118 50 48 41
40 118 49 57 40 118 49 56 41 41 41 40 118 49 55 41 41 41))()COMPLETE)(|pbor_| THM((
TTREE 62 62 32(|PBool|)32 45 62 32(|PBool|)32 45 62 32(|PBool|)0)((TTREE(|wf|(TTREE 69
120 112 108 105 99 105 116 73 32 0 39(|l2|(TTREE 112 98 49)(TTREE 112 98 50)(
TTREE 0(|PBool_cases|(TTREE 112 98 49 0)(TTREE(|bool|(TTREE(|btrue|)))0 32 32)(TTREE 
112 98 50 0 32 32)(TTREE(|l|(TTREE 81 49)(TTREE(|PBool_cases|(TTREE 112 98 50)(TTREE(
|bool|(TTREE(|btrue|))))(TTREE(|prop|(TTREE 81 49))0 32 32 32 32 32 32 32 32 32 32 32
32 32 32 32 32 32 32 32 32 32 32 32 32)(TTREE(|l|(TTREE 81 50)(TTREE(|prop|(TTREE(
|or|(TTREE 81 49)(TTREE 81 50))))))))))))))39 32 0))0)NIL)(TTREE(|l2|(TTREE 112 98 49)(TTREE 112 98 
50)(TTREE 0(|PBool_cases|(TTREE 112 98 49 0)(TTREE(|bool|(TTREE(|btrue|)))0 32 32)(TTREE
112 98 50 0 32 32)(TTREE(|l|(TTREE 81 49)(TTREE(|PBool_cases|(TTREE 112 98 50)(TTREE(
|bool|(TTREE(|btrue|))))(TTREE(|prop|(TTREE 81 49))0 32 32 32 32 32 32 32 32 32 32 32
32 32 32 32 32 32 32 32 32 32 32 32 32)(TTREE(|l|(TTREE 81 50)(TTREE(|prop|(TTREE(
|or|(TTREE 81 49)(TTREE 81 50))))))))))))))))()COMPLETE)(|pbor| DEF(TTREE 60 80 58 80 66 111 111 
108 62 32 173 32 60 81 58 80 66 111 111 108 62 61 61(|ap|(TTREE(|ap|(TTREE(|e|(
TTREE 112 98 111 114)))(TTREE 60 80 62)))(TTREE 60 81 62))))(|pbor_char| THM((TTREE 62 62
32(|all2|(TTREE 112 98 49)(TTREE 112 98 50)(TTREE(|PBool|))(TTREE 0 32 32(|iff|(TTREE(
|is_pbtrue|(TTREE(|pbor|(TTREE 112 98 49)(TTREE 112 98 50)))))(TTREE(|or|(TTREE(
|is_pbtrue|(TTREE 112 98 49)))(TTREE(|is_pbtrue|(TTREE 112 98 50))))))))0 0)((TTREE(|wf|(TTREE
79 110 86 97 114 32 96 112 98 49 96 32 80 66 111 111 108 69 32 84 72 69 78
87 32 79 110 86 97 114 32 96 112 98 50 96 32 80 66 111 111 108 69 32 84 72
69 78 87 32 69 118 97 108 67 111 110 99 108 32))0 84 72 69 78 32 84 114 121 
32(|wf|(TTREE 79 114 66 121 72 121 112 32))0)(((TTREE(|wf|(TTREE 79 110 76 97 115 116
72 121 112 32 69 32))0)NIL)((TTREE(|wf|(TTREE 79 110 76 97 115 116 72 121 112 32 69
32))0)NIL)((TTREE(|wf|(TTREE 79 110 76 97 115 116 72 121 112 32 69 32))0)NIL)))(TTREE 92 
112 98 49 46 100 101 99 105 100 101 40 112 98 49 59 97 49 46 100 101 99 105
100 101 40 97 49 59 97 50 46 92 112 98 50 46 100 101 99 105 100 101 40 112
98 50 59 97 51 46 100 101 99 105 100 101 40 97 51 59 97 52 46 40 92 118 48
46 40 92 118 49 46 60 118 48 44 118 49 62 41 40 92 118 51 46 97 50 41 41 40
92 118 50 46 105 110 108 40 97 50 41 41 59 98 53 46 40 92 118 52 46 40 92 
118 53 46 60 118 52 44 118 53 62 41 40 92 118 55 46 97 50 41 41 40 92 118 
54 46 105 110 108 40 97 50 41 41 41 59 98 52 46 40 92 118 56 46 40 92 118 
57 46 60 118 56 44 118 57 62 41 40 92 118 49 49 46 97 50 41 41 40 92 118 49
48 46 105 110 108 40 97 50 41 41 41 59 98 51 46 92 112 98 50 46 100 101 99
105 100 101 40 112 98 50 59 97 52 46 100 101 99 105 100 101 40 97 52 59 97
53 46 40 92 118 49 50 46 40 92 118 49 51 46 60 118 49 50 44 118 49 51 62 41
40 92 118 49 53 46 98 51 41 41 40 92 118 49 52 46 105 110 114 40 98 51 41 
41 59 98 54 46 40 92 118 49 54 46 40 92 118 49 55 46 60 118 49 54 44 118 49
55 62 41 40 92 118 49 57 46 100 101 99 105 100 101 40 118 49 57 59 118 50 
48 46 97 110 121 40 118 50 48 41 59 118 50 49 46 97 110 121 40 118 50 49 41
41 41 41 40 92 118 49 56 46 97 110 121 40 118 49 56 41 41 41 59 98 53 46 40
92 118 50 50 46 40 92 118 50 51 46 60 118 50 50 44 118 50 51 62 41 40 92 
118 50 53 46 100 101 99 105 100 101 40 118 50 53 59 118 50 54 46 97 110 121
40 118 50 54 41 59 118 50 55 46 118 50 55 41 41 41 40 92 118 50 52 46 105 
110 114 40 118 50 52 41 41 41 41 59 98 50 46 92 112 98 50 46 100 101 99 105
100 101 40 112 98 50 59 97 51 46 100 101 99 105 100 101 40 97 51 59 97 52 
46 40 92 118 50 56 46 40 92 118 50 57 46 60 118 50 56 44 118 50 57 62 41 40
92 118 51 49 46 97 52 41 41 40 92 118 51 48 46 105 110 114 40 97 52 41 41 
59 98 53 46 40 92 118 51 50 46 40 92 118 51 51 46 60 118 51 50 44 118 51 51
62 41 40 92 118 51 53 46 100 101 99 105 100 101 40 118 51 53 59 118 51 54 
46 118 51 54 59 118 51 55 46 97 110 121 40 118 51 55 41 41 41 41 40 92 118
51 52 46 105 110 108 40 118 51 52 41 41 41 59 98 52 46 40 92 118 51 56 46 
40 92 118 51 57 46 60 118 51 56 44 118 51 56 62 41 40 118 51 56 41 41 40 92
118 52 48 46 118 52 48 41 41 41))()COMPLETE)(|pb_all_elements_| THM((TTREE 62 62 32
79 98 106 101 99 116 0)((TTREE(|t|(TTREE 69 120 112 108 105 99 105 116 73 32 39(
|l3|(TTREE 65)(TTREE 81)(TTREE 108)(TTREE(|list_rec|(TTREE(|bool|(TTREE(|btrue|))))(TTREE 
104)(TTREE 116)(TTREE 118)(TTREE(|pband|(TTREE 81 40 104 41)(TTREE 118)))(TTREE 108))))39))0 0)
NIL)(TTREE(|l3|(TTREE 65)(TTREE 81)(TTREE 108)(TTREE(|list_rec|(TTREE(|bool|(TTREE(|btrue|))))(
TTREE 104)(TTREE 116)(TTREE 118)(TTREE(|pband|(TTREE 81 40 104 41)(TTREE 118)))(TTREE 108))))))()
COMPLETE)(|pb_all_elements| DEF(TTREE 162 148 32 60 108 58 108 105 115 116 62
32 58 32 60 65 58 116 121 112 101 62 32 108 105 115 116 46 32 60 81 58 112
98 45 112 114 101 100 62 61 61(|nothing|(TTREE 0))(|ap|(TTREE(|ap|(TTREE(|ap|(TTREE(
|e|(TTREE 112 98 95 97 108 108 95 101 108 101 109 101 110 116 115)))(TTREE 60 65
62)))(TTREE 60 81 62)))(TTREE 60 108 62))))(|pb_all_elements__| THM((TTREE 62 62 32(|all|(
TTREE 65)(TTREE(|Type|))(TTREE(|all|(TTREE 80)(TTREE 65 45 62(|PBool|))(TTREE(|all|(TTREE 
108)(TTREE 65 32 108 105 115 116)(TTREE 40(|pb_all_elements|(TTREE 108)(TTREE 65)(
TTREE 80))41 32 105 110 32(|PBool|)))))))0)((TTREE(|ts|(TTREE 85 110 102 111 108 100 32 96
112 98 95 97 108 108 95 101 108 101 109 101 110 116 115 96 32))0)NIL)(TTREE 92 
65 46 92 80 46 92 108 46 97 120 105 111 109))()COMPLETE)(|pb_all_elements_char| 
THM((TTREE 62 62 32(|all|(TTREE 65)(TTREE(|Top|))(TTREE(|all|(TTREE 80)(TTREE 65 45 62(
|PBool|))(TTREE(|all|(TTREE 108)(TTREE(|list|(TTREE 65)))(TTREE 0 32 32(|iff|(TTREE(
|is_pbtrue|(TTREE(|pb_all_elements|(TTREE 108)(TTREE 65)(TTREE 80))))0 32)(TTREE(
|all_elements|(TTREE 108)(TTREE 65)(TTREE(|l|(TTREE 97)(TTREE(|is_pbtrue|(TTREE 80 40
97 41))))))))))))))0)((TTREE(F(TTREE(|ww|(TTREE 79 110 86 97 114 32 96 108 96 32 69 32))))0)(((TTREE(|wf|(
TTREE 69 118 97 108 67 111 110 99 108 32))0)NIL)((TTREE(|wf|(TTREE 85 110 114 111 
108 108 68 101 102 115 73 110 67 111 110 99 108 32 96 96 112 98 95 97 108 
108 95 101 108 101 109 101 110 116 115 32 97 108 108 95 101 108 101 109 101
110 116 115 96 96 32))0)(((TTREE(|wf|(TTREE 70 76 101 109 109 97 32 96 112 98 97 
110 100 95 99 104 97 114 96 32 91 55 93 32))0)NIL)((TTREE(|wf|(TTREE 70 76 101 109
109 97 32 96 112 98 97 110 100 95 99 104 97 114 96 32 91 55 93 32))32 84 72 
69 78 32(|wf|(TTREE 66 97 99 107 99 104 97 105 110 32 32))0)NIL)((TTREE(|wf|(TTREE 76
101 109 109 97 32 96 112 98 97 110 100 95 99 104 97 114 96 32))32 84 72 69 78
32(|wf|(TTREE 66 97 99 107 99 104 97 105 110 32))0)NIL)))))(TTREE 92 65 46 92 80 46 92
108 46 108 105 115 116 95 105 110 100 40 108 59 40 92 118 49 46 40 92 118 
50 46 60 118 49 44 118 49 62 41 40 118 49 41 41 40 92 118 51 46 118 51 41 
59 104 53 44 108 44 118 48 46 115 112 114 101 97 100 40 118 48 59 118 52 44
118 53 46 40 92 118 54 46 40 92 118 55 46 60 118 54 44 118 55 62 41 40 92 
118 50 55 46 115 112 114 101 97 100 40 118 50 55 59 118 50 56 44 118 50 57
46 40 92 118 51 48 46 40 92 118 51 49 46 40 92 118 51 50 46 115 112 114 101
97 100 40 118 51 50 59 118 51 51 44 118 51 52 46 40 92 118 51 53 46 118 51
53 41 40 118 51 52 40 40 92 118 51 54 46 40 92 118 51 55 46 60 118 50 56 44
118 51 55 62 41 40 40 92 118 51 56 46 40 92 118 51 57 46 118 51 57 41 40 
118 51 56 40 118 50 57 41 41 41 40 118 53 41 41 41 40 118 50 56 41 41 41 41
41 40 118 51 49 40 116 101 114 109 95 111 102 40 112 98 95 97 108 108 95 
101 108 101 109 101 110 116 115 95 41 40 65 41 40 80 41 40 108 41 41 41 41
40 118 51 48 40 80 40 104 53 41 41 41 41 40 116 101 114 109 95 111 102 40 
112 98 97 110 100 95 99 104 97 114 41 41 41 41 41 40 92 118 56 46 40 92 118
57 46 40 92 118 49 48 46 60 118 57 44 118 49 48 62 41 40 40 92 118 49 56 46
40 92 118 49 57 46 115 112 114 101 97 100 40 118 49 57 59 118 50 48 44 118
50 49 46 40 92 118 50 50 46 115 112 114 101 97 100 40 118 50 50 59 118 50 
51 44 118 50 52 46 40 92 118 50 53 46 40 92 118 50 54 46 118 50 54 41 40 
118 50 53 40 118 50 52 41 41 41 40 118 52 41 41 41 40 118 50 48 40 118 56 
41 41 41 41 40 118 49 56 40 116 101 114 109 95 111 102 40 112 98 95 97 108
108 95 101 108 101 109 101 110 116 115 95 41 40 65 41 40 80 41 40 108 41 41
41 41 40 116 101 114 109 95 111 102 40 112 98 97 110 100 95 99 104 97 114 
41 40 80 40 104 53 41 41 41 41 41 40 40 92 118 49 49 46 40 92 118 49 50 46
115 112 114 101 97 100 40 118 49 50 59 118 49 51 44 118 49 52 46 40 92 118
49 53 46 115 112 114 101 97 100 40 118 49 53 59 118 49 54 44 118 49 55 46 
118 49 54 41 41 40 118 49 51 40 118 56 41 41 41 41 40 118 49 49 40 116 101
114 109 95 111 102 40 112 98 95 97 108 108 95 101 108 101 109 101 110 116 
115 95 41 40 65 41 40 80 41 40 108 41 41 41 41 40 116 101 114 109 95 111 
102 40 112 98 97 110 100 95 99 104 97 114 41 40 80 40 104 53 41 41 41 41 41
41 41))()COMPLETE)(|pb_Int_eq_| THM((TTREE 62 62 32 73 110 116 32 45 62 32 73 110 
116 32 45 62 32(|PBool|))((TTREE(|wf|(TTREE 69 120 112 108 105 99 105 116 73 32 39(
|l2|(TTREE 109)(TTREE 110)(TTREE(|if_eq|(TTREE 109)(TTREE 110)(TTREE(|bool|(TTREE(|btrue|))))(
TTREE(|bool|(TTREE(|bfalse|)))))))39 32))0)NIL)(TTREE(|l2|(TTREE 109)(TTREE 110)(TTREE(|if_eq|(
TTREE 109)(TTREE 110)(TTREE(|bool|(TTREE(|btrue|))))(TTREE(|bool|(TTREE(|bfalse|)))))))))()COMPLETE)(
|pb_Int_eq| DEF(TTREE 60 120 58 105 110 116 62 61 60 121 58 105 110 116 62 
61 61(|ap|(TTREE(|ap|(TTREE(|e|(TTREE 112 98 95 73 110 116 95 101 113)))(TTREE 60 120
62)))(TTREE 60 121 62))))(|pb_Int_eq_char| THM((TTREE 62 62 32(|all2|(TTREE 109)(TTREE 110)(
TTREE 73 110 116)(TTREE(|iff|(TTREE(|is_pbtrue|(TTREE(|pb_Int_eq|(TTREE 109)(TTREE 
110)))))(TTREE(|eq|(TTREE 109)(TTREE 110))))))0)((TTREE(F(TTREE(|ww|(TTREE 82 101 112 101 97 116 
70 111 114 32 50 32 73 32))))0)(((TTREE(|wc|(TTREE 68 101 99 105 115 105 111 110 84 
101 114 109 67 97 115 101 115 32 91 39(|if_eq|(TTREE 109)(TTREE 110)(TTREE(|bool|(
TTREE(|btrue|))))(TTREE(|bool|(TTREE(|bfalse|)))))39 44 32 39(|PBool|)39 93 32))0 84 72 69 78
32(F(TTREE 85 110 102 111 108 100 32 96 112 98 95 73 110 116 95 101 113 96))0 0
0)(((TTREE(|wf|(TTREE 83 117 98 115 116 70 111 114 32 40 104 32 52 32 112 41 32 
84 72 69 78 32 73 102 84 104 101 110 79 110 67 111 110 99 108 32 105 115 95
97 110 100 95 116 101 114 109 32 69 118 97 108 67 111 110 99 108 32))0 0)NIL)((
TTREE(|wf|(TTREE 83 117 98 115 116 70 111 114 32 40 104 32 52 32 112 114 108
103 111 97 108 41 32 84 72 69 78 32 73 102 84 104 101 110 79 110 67 111 110
99 108 32 105 115 95 97 110 100 95 116 101 114 109 32 69 118 97 108 67 111
110 99 108 32))0 84 72 69 78 32(|wf|(TTREE 67 111 110 116 114 97 100 105 99 116
105 111 110 32))0)NIL)))))(TTREE 92 109 46 92 110 46 40 92 118 48 46 100 101 99 105
100 101 40 118 48 59 118 50 46 40 92 118 52 46 40 92 118 53 46 40 92 118 54
46 60 118 53 44 118 54 62 41 40 92 118 56 46 97 120 105 111 109 41 41 40 92
118 55 46 118 50 41 41 40 97 120 105 111 109 41 59 118 51 46 40 92 118 57 
46 40 92 118 49 48 46 40 92 118 49 49 46 60 118 49 48 44 118 51 62 41 40 
118 51 41 41 40 92 118 49 50 46 97 110 121 40 118 49 50 41 41 41 40 97 120
105 111 109 41 41 41 40 105 110 116 95 101 113 40 109 59 110 59 105 110 108
40 97 120 105 111 109 41 59 105 110 114 40 97 120 105 111 109 41 41 41))()
COMPLETE)(|pb_Atom_eq_| THM((TTREE 62 62 32 65 116 111 109 32 45 62 32 65 116 
111 109 32 45 62 32(|PBool|))((TTREE(|wf|(TTREE 69 120 112 108 105 99 105 116 73 
32 39(|l2|(TTREE 97)(TTREE 98)(TTREE(|if_aeq|(TTREE 97)(TTREE 98)(TTREE(|bool|(TTREE(
|btrue|))))(TTREE(|bool|(TTREE(|bfalse|)))))))39 32))0)NIL)(TTREE(|l2|(TTREE 97)(TTREE 98)(TTREE(
|if_aeq|(TTREE 97)(TTREE 98)(TTREE(|bool|(TTREE(|btrue|))))(TTREE(|bool|(TTREE(|bfalse|)))))))))()
COMPLETE)(|pb_Atom_eq| DEF(TTREE 60 120 58 65 116 111 109 62 61 60 121 58 65 
116 111 109 62 61 61(|ap|(TTREE(|ap|(TTREE(|e|(TTREE 112 98 95 65 116 111 109 95
101 113)))(TTREE 60 120 62)))(TTREE 60 121 62))))(|pb_Atom_eq_char| THM((TTREE 62 62 32(
|all2|(TTREE 97)(TTREE 98)(TTREE 65 116 111 109)(TTREE(|iff|(TTREE(|is_pbtrue|(TTREE(
|pb_Atom_eq|(TTREE 97)(TTREE 98)))))(TTREE 40 97 61 98 32 105 110 32 65 116 111 109
41))))0)((TTREE(F(TTREE(|ww|(TTREE 82 101 112 101 97 116 70 111 114 32 50 32 73 32))))0 0)(((
TTREE(|wc|(TTREE 68 101 99 105 115 105 111 110 84 101 114 109 67 97 115 101 
115 32 91 39(|if_aeq|(TTREE 97)(TTREE 98)(TTREE(|bool|(TTREE(|btrue|))))(TTREE(|bool|(TTREE(
|bfalse|)))))39 44 32 39(|PBool|(TTREE 80))39 93 32))0 84 72 69 78 32(F(TTREE 85 110 102
111 108 100 32 96 112 98 95 65 116 111 109 95 101 113 96))0)(((TTREE(|wf|(TTREE 83
117 98 115 116 70 111 114 32 40 104 32 52 32 112 41 32 84 72 69 78 32 73 
102 84 104 101 110 79 110 67 111 110 99 108 32 105 115 95 97 110 100 95 116
101 114 109 32 69 118 97 108 67 111 110 99 108 32))0)NIL)((TTREE(|wf|(TTREE 83 117
98 115 116 70 111 114 32 40 104 32 52 32 112 41 32 84 72 69 78 32 73 102 84
104 101 110 79 110 67 111 110 99 108 32 105 115 95 97 110 100 95 116 101 
114 109 32 69 118 97 108 67 111 110 99 108 32))0 84 72 69 78 32(|wf|(TTREE 67 
111 110 116 114 97 100 105 99 116 105 111 110 32))0)NIL)))))(TTREE 92 97 46 92 98 46
40 92 118 48 46 100 101 99 105 100 101 40 118 48 59 118 52 46 40 92 118 54
46 40 92 118 55 46 40 92 118 56 46 60 118 55 44 118 56 62 41 40 92 118 49 
48 46 97 120 105 111 109 41 41 40 92 118 57 46 118 52 41 41 40 97 120 105 
111 109 41 59 118 53 46 40 92 118 49 49 46 40 92 118 49 50 46 40 92 118 49
51 46 60 118 49 50 44 118 53 62 41 40 118 53 41 41 40 92 118 49 52 46 97 
110 121 40 118 49 52 41 41 41 40 97 120 105 111 109 41 41 41 40 40 92 118 
49 46 40 92 118 50 46 40 92 118 51 46 118 51 41 40 118 50 40 98 41 41 41 40
118 49 40 97 41 41 41 40 116 101 114 109 95 111 102 40 65 116 111 109 95 
101 113 95 100 101 99 105 100 97 98 108 101 41 41 41))()COMPLETE)(|pb_of_decide_|
THM((TTREE 62 62 32 79 98 106 101 99 116)((TTREE(|wf|(TTREE 69 120 112 108 105 99
105 116 73 32 39(|l|(TTREE 100)(TTREE(|dec|(TTREE 100)(TTREE 117)(TTREE(|bool|(TTREE(
|btrue|))))(TTREE 117)(TTREE(|bool|(TTREE(|bfalse|)))))))39 32))0)NIL)(TTREE(|l|(TTREE 100)(TTREE(
|dec|(TTREE 100)(TTREE 117)(TTREE(|bool|(TTREE(|btrue|))))(TTREE 117)(TTREE(|bool|(TTREE(
|bfalse|)))))))))()COMPLETE)(|pb_of_decide| DEF(TTREE 112 98 95 111 102 95 100 101 99 105
100 101 40 60 100 58 80 173 147 80 62 41 61 61(|ap|(TTREE(|e|(TTREE 112 98 95 
111 102 95 100 101 99 105 100 101)))(TTREE 60 100 62))))(|pb_of_decide__| THM((TTREE 
62 62 32(|all|(TTREE 80)(TTREE(|Type|))(TTREE(|all|(TTREE 100)(TTREE 40(|or|(TTREE 80)(
TTREE(|not|(TTREE 80))))41)(TTREE(|pb_of_decide|(TTREE 100))32 105 110 32(|PBool|)))))0)((TTREE(
|wf|(TTREE 85 110 102 111 108 100 32 96 112 98 95 111 102 95 100 101 99 105
100 101 96 32))0)NIL)(TTREE 92 80 46 92 100 46 97 120 105 111 109))()COMPLETE)(
|pb_of_decide_char| THM((TTREE 62 62 32(|all|(TTREE 80)(TTREE(|Type|))(TTREE(|all|(
TTREE 100)(TTREE 40(|or|(TTREE 80)(TTREE(|not|(TTREE 80))))41)(TTREE(|iff|(TTREE(|is_pbtrue|(
TTREE(|pb_of_decide|(TTREE 100)))))(TTREE 80))))))0)((TTREE(|wf|(TTREE 79 110 86 97 114 32 96
100 96 32 69 32 84 72 69 78 32 69 118 97 108 67 111 110 99 108 32))0)NIL)(TTREE
92 80 46 92 100 46 100 101 99 105 100 101 40 100 59 97 51 46 40 92 118 48 
46 40 92 118 49 46 60 118 48 44 118 49 62 41 40 92 118 51 46 97 120 105 111
109 41 41 40 92 118 50 46 97 51 41 59 98 52 46 40 92 118 52 46 40 92 118 53
46 60 118 52 44 98 52 62 41 40 98 52 41 41 40 92 118 54 46 97 110 121 40 
118 54 41 41 41))()COMPLETE)(|PBoolChar| ML(TTREE 108 101 116 32 80 66 111 111 108
67 104 97 114 95 108 101 109 109 97 115 32 61 32 0 96 96 112 98 97 110 100
95 99 104 97 114 32 112 98 99 97 110 100 95 99 104 97 114 32 112 98 111 114
95 99 104 97 114 32 112 98 95 97 108 108 95 101 108 101 109 101 110 116 115
95 99 104 97 114 32 112 98 95 73 110 116 95 101 113 95 99 104 97 114 32 112
98 95 65 116 111 109 95 101 113 95 99 104 97 114 32 112 98 95 111 102 95 
100 101 99 105 100 101 95 99 104 97 114 32 32 112 98 110 111 116 95 99 104
97 114 96 96 32 59 59 32 0 0 108 101 116 32 80 66 111 111 108 67 104 97 114
32 61 32 70 105 114 115 116 32 40 109 97 112 32 76 101 109 109 97 32 80 66
111 111 108 67 104 97 114 95 108 101 109 109 97 115 41 32 59 59 32 0 0 108
101 116 32 70 80 66 111 111 108 67 104 97 114 32 105 32 61 32 70 105 114 
115 116 32 40 109 97 112 32 40 92 120 46 32 70 76 101 109 109 97 32 120 32
91 105 93 41 32 80 66 111 111 108 67 104 97 114 95 108 101 109 109 97 115 
41 32 59 59 32 0))(|END_PBool| DEF(TTREE 61 61)))