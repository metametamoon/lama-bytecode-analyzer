To run on a performance test: 
```
make Sort
```

Output:
```
cnt=31: DROP; (block_length=1B)
cnt=28: DUP; (block_length=1B)
cnt=21: ELEM; (block_length=1B)
cnt=16: CONST   1; (block_length=5B)
cnt=13: CONST   1;ELEM; (block_length=6B)
cnt=12: CONST   0; (block_length=5B)
cnt=11: DROP;DUP; (block_length=2B)
cnt=11: DUP;CONST       1; (block_length=6B)
cnt=10: DROP;DROP; (block_length=2B)
cnt=8: CONST    0;ELEM; (block_length=6B)
cnt=8: LD       A(0); (block_length=5B)
cnt=7: DUP;CONST        0; (block_length=6B)
cnt=7: ELEM;DROP; (block_length=2B)
cnt=6: END; (block_length=1B)
cnt=4: DUP;DUP; (block_length=2B)
cnt=4: SEXP     cons 2; (block_length=9B)
cnt=3: ELEM;ST  L(0); (block_length=6B)
cnt=3: CALL     0x0000015f 1; (block_length=9B)
cnt=3: LD       L(3); (block_length=5B)
cnt=3: DUP;ARRAY        2; (block_length=6B)
cnt=3: LD       L(0); (block_length=5B)
cnt=3: ST       L(0);DROP; (block_length=6B)
cnt=3: ST       L(0); (block_length=5B)
cnt=3: CALL     Barray  2;JMP   0x00000308; (block_length=10B)
cnt=3: JMP      0x00000308; (block_length=5B)
cnt=3: ARRAY    2; (block_length=5B)
cnt=3: CALL     Barray  2; (block_length=5B)
cnt=2: SEXP     cons 2;CALL     Barray  2; (block_length=14B)
cnt=2: CALL     0x00000097 1; (block_length=9B)
cnt=2: TAG      cons 2; (block_length=9B)
cnt=2: ELEM;CONST       0; (block_length=6B)
cnt=2: BINOP    -; (block_length=1B)
cnt=2: DUP;TAG  cons 2; (block_length=10B)
cnt=2: CALL     0x0000002b 1; (block_length=9B)
cnt=2: LD       L(1); (block_length=5B)
cnt=2: ELEM;CONST       1; (block_length=6B)
cnt=2: BEGIN    2 0; (block_length=9B)
cnt=2: JMP      0x00000074; (block_length=5B)
cnt=2: JMP      0x0000015e; (block_length=5B)
cnt=2: BEGIN    1 0; (block_length=9B)
cnt=2: BINOP    ==; (block_length=1B)
cnt=1: SEXP     cons 2;CALL     0x0000015f 1; (block_length=18B)
cnt=1: LD       A(0);CONST      1; (block_length=10B)
cnt=1: ELEM;SEXP        cons 2; (block_length=10B)
cnt=1: LD       L(0);JMP        0x0000015e; (block_length=10B)
cnt=1: LD       L(1);LD L(3); (block_length=10B)
cnt=1: LD       L(3);LD L(0); (block_length=10B)
cnt=1: LD       L(3);LD L(1); (block_length=10B)
cnt=1: LD       L(3);LD L(4); (block_length=10B)
cnt=1: LD       L(5);LD L(3); (block_length=10B)
cnt=1: ST       L(4);DROP; (block_length=6B)
cnt=1: ST       L(5);DROP; (block_length=6B)
cnt=1: CONST    1;LINE  10; (block_length=10B)
cnt=1: CONST    0;LINE  13; (block_length=10B)
cnt=1: CONST    0;JMP   0x00000074; (block_length=10B)
cnt=1: BINOP    -;CALL  0x0000002b 1; (block_length=10B)
cnt=1: FAIL     189; (block_length=9B)
cnt=1: FAIL     1117; (block_length=9B)
cnt=1: BEGIN    1 1; (block_length=9B)
cnt=1: CALL     0x00000075 1; (block_length=9B)
cnt=1: BEGIN    1 6; (block_length=9B)
cnt=1: CALL     0x00000309 2; (block_length=9B)
cnt=1: LD       A(0);CALL       0x0000015f 1; (block_length=14B)
cnt=1: LINE     29;LINE 31; (block_length=10B)
cnt=1: LINE     31;CONST        1000; (block_length=10B)
cnt=1: CONST    1000;CALL       0x0000002b 1; (block_length=14B)
cnt=1: SEXP     cons 2;JMP      0x00000074; (block_length=14B)
cnt=1: LD       L(0);SEXP       cons 2; (block_length=14B)
cnt=1: LD       L(0);CALL       0x00000097 1; (block_length=14B)
cnt=1: LD       L(1);CALL       0x00000309 2; (block_length=14B)
cnt=1: LD       L(2);CALL       0x0000015f 1; (block_length=14B)
cnt=1: LD       L(4);SEXP       cons 2; (block_length=14B)
cnt=1: LINE     28;LD   A(0); (block_length=10B)
cnt=1: LD       A(0);CALL       0x00000097 1; (block_length=14B)
cnt=1: BEGIN    1 0;LINE        22; (block_length=14B)
cnt=1: BEGIN    1 0;LINE        28; (block_length=14B)
cnt=1: BEGIN    1 1;LINE        18; (block_length=14B)
cnt=1: BEGIN    1 6;LINE        7; (block_length=14B)
cnt=1: BEGIN    2 0;LINE        1; (block_length=14B)
cnt=1: BEGIN    2 0;LINE        29; (block_length=14B)
cnt=1: TAG      cons 2;CJMPz    0x00000188; (block_length=14B)
cnt=1: TAG      cons 2;CJMPz    0x000001ac; (block_length=14B)
cnt=1: LINE     9;LD    L(3); (block_length=10B)
cnt=1: LD       A(0);CJMPz      0x0000006a; (block_length=10B)
cnt=1: LD       A(0);LINE       2; (block_length=10B)
cnt=1: LD       A(0);CALL       Barray  2; (block_length=10B)
cnt=1: ARRAY    2;CJMPz 0x00000118; (block_length=10B)
cnt=1: ARRAY    2;CJMPz 0x0000028b; (block_length=10B)
cnt=1: ARRAY    2;CJMPz 0x000000c5; (block_length=10B)
cnt=1: LINE     1;LD    A(0); (block_length=10B)
cnt=1: LINE     2;LD    A(1); (block_length=10B)
cnt=1: LINE     7;LD    A(0); (block_length=10B)
cnt=1: LD       A(0);LD A(0); (block_length=10B)
cnt=1: LINE     10;LD   L(1); (block_length=10B)
cnt=1: LINE     11;LD   L(2); (block_length=10B)
cnt=1: LINE     13;LD   A(0); (block_length=10B)
cnt=1: LINE     18;LD   A(0); (block_length=10B)
cnt=1: LINE     19;LD   L(0); (block_length=10B)
cnt=1: LINE     20;LD   L(0); (block_length=10B)
cnt=1: LINE     22;LINE 24; (block_length=10B)
cnt=1: LINE     24;LD   A(0); (block_length=10B)
cnt=1: CJMPz    0x0000028b; (block_length=5B)
cnt=1: ST       L(4); (block_length=5B)
cnt=1: ST       L(5); (block_length=5B)
cnt=1: CJMPz    0x00000112; (block_length=5B)
cnt=1: CJMPz    0x00000266; (block_length=5B)
cnt=1: CJMPz    0x0000006a; (block_length=5B)
cnt=1: CJMPz    0x000000bf; (block_length=5B)
cnt=1: CJMPz    0x00000118; (block_length=5B)
cnt=1: CJMPz    0x00000188; (block_length=5B)
cnt=1: ST       L(3); (block_length=5B)
cnt=1: CJMPz    0x000001ac; (block_length=5B)
cnt=1: CJMPz    0x000000c5; (block_length=5B)
cnt=1: LINE     1; (block_length=5B)
cnt=1: LINE     2; (block_length=5B)
cnt=1: LINE     7; (block_length=5B)
cnt=1: LINE     9; (block_length=5B)
cnt=1: LINE     10; (block_length=5B)
cnt=1: LINE     11; (block_length=5B)
cnt=1: JMP      0x000002d9; (block_length=5B)
cnt=1: BINOP    >; (block_length=1B)
cnt=1: BINOP    -;END; (block_length=2B)
cnt=1: DUP;DROP; (block_length=2B)
cnt=1: ELEM;DUP; (block_length=2B)
cnt=1: CONST    1000; (block_length=5B)
cnt=1: JMP      0x00000106; (block_length=5B)
cnt=1: JMP      0x00000150; (block_length=5B)
cnt=1: JMP      0x00000182; (block_length=5B)
cnt=1: LINE     13; (block_length=5B)
cnt=1: JMP      0x000002ec; (block_length=5B)
cnt=1: LD       L(2); (block_length=5B)
cnt=1: LD       L(4); (block_length=5B)
cnt=1: LD       L(5); (block_length=5B)
cnt=1: LD       A(1); (block_length=5B)
cnt=1: ST       L(1); (block_length=5B)
cnt=1: ST       L(2); (block_length=5B)
cnt=1: ELEM;ST  L(1); (block_length=6B)
cnt=1: DROP;JMP 0x00000150; (block_length=6B)
cnt=1: DROP;JMP 0x00000182; (block_length=6B)
cnt=1: DROP;JMP 0x000002d9; (block_length=6B)
cnt=1: DROP;JMP 0x000002ec; (block_length=6B)
cnt=1: DROP;LD  L(5); (block_length=6B)
cnt=1: DROP;LINE        9; (block_length=6B)
cnt=1: DROP;LINE        19; (block_length=6B)
cnt=1: DROP;LINE        20; (block_length=6B)
cnt=1: DROP;JMP 0x00000106; (block_length=6B)
cnt=1: ELEM;ST  L(2); (block_length=6B)
cnt=1: ELEM;ST  L(3); (block_length=6B)
cnt=1: ELEM;ST  L(4); (block_length=6B)
cnt=1: ELEM;ST  L(5); (block_length=6B)
cnt=1: LD       A(0);DUP; (block_length=6B)
cnt=1: LD       A(1);BINOP      -; (block_length=6B)
cnt=1: ST       L(1);DROP; (block_length=6B)
cnt=1: ST       L(2);DROP; (block_length=6B)
cnt=1: BINOP    >;CJMPz 0x00000266; (block_length=6B)
cnt=1: LINE     18; (block_length=5B)
cnt=1: LINE     19; (block_length=5B)
cnt=1: LINE     20; (block_length=5B)
cnt=1: LINE     22; (block_length=5B)
cnt=1: LINE     24; (block_length=5B)
cnt=1: LINE     28; (block_length=5B)
cnt=1: LINE     29; (block_length=5B)
cnt=1: LINE     31; (block_length=5B)
cnt=1: ST       L(3);DROP; (block_length=6B)
cnt=1: BINOP    ==;CJMPz        0x00000112; (block_length=6B)
cnt=1: BINOP    ==;CJMPz        0x000000bf; (block_length=6B)
cnt=1: CONST    0;BINOP >; (block_length=6B)
cnt=1: CONST    0;BINOP ==; (block_length=6B)
cnt=1: CONST    1;BINOP -; (block_length=6B)
cnt=1: CONST    1;BINOP ==; (block_length=6B)
cnt=1: DROP;CONST       0; (block_length=6B)
```