# A named parameter's default is its function's: it has only the heap
# effects the function's own allow, and neither fails nor suspends, also of
# a <decides> or <suspends> function (Book of Verse tests,
# DefaultNamed.versetest 805-878). Within those, a default may read, write
# and construct as its function may.
reads_class := class<reads>{ N:int = 1 }
cell := class{ var N:int = 0 }
Bump(C:cell)<transacts>:int = block{ set C.N += 1; C.N }
Limit(A:int, B:int, ?C:int = 42)<computes><decides>:int = A + B <= C
Make(?C:reads_class = reads_class{})<reads>:int = C.N
Count(C:cell, ?K:int = Bump(C))<transacts>:int = K + C.N
Later(?D:float = 1.5)<suspends>:float = block{ Sleep(0.0); D }
Main()<suspends>:void =
    if (V := Limit[1, 2]) then Print("{V}") else Print("fail")
    if (V := Limit[1, 2, ?C := 2]) then Print("{V}") else Print("fail")
    Print("{Make()}")
    C := cell{}
    Print("{Count(C)}")
    Print("{Count(C, ?K := 10)}")
    Print("{Later()}")
