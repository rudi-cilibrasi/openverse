counter:=class<allocates>{var N:int=0}
Make(C:counter)<transacts>:[int]int=
    set C.N+=1
    Print("make {C.N}")
    map{2=>7,1=>8}
Widen(M:[int]int)<computes>:[rational]rational=M
KeysOnly(M:[int]string)<computes>:[rational]string=M
ValuesOnly(M:[int]int)<computes>:[int]rational=M
Main():void=
    C:=counter{}
    M:=Widen(Make(C))
    if(V:=M[2],V=7):Print("key 2 value 7")
    if(V:=M[1],V=8):Print("key 1 value 8")
    Print("entries {M.Length} count {C.N}")
    E:[int]int=map{}
    Print("empty {Widen(E).Length}")
    K:=KeysOnly(map{3=>"key only"})
    if(V:=K[3]):Print(V)
    Vals:=ValuesOnly(map{4=>9})
    if(V:=Vals[4],V=9):Print("value only 9")
    if(Widen(Make(C)),false?)then Print("bad")else Print("rolled")
    Print("after {C.N}")
