ArrayUp(X:[]int)<computes>:[]rational=X
OptionUp(X:?int)<computes>:?rational=X
MapUp(X:[int]int)<computes>:[int]rational=X
TupleUp(X:tuple(int,string))<computes>:tuple(rational,string)=X
Main():void=
    A:=ArrayUp(array{7})
    if(N:=A[0],N=7):Print("array peer")
    O:=OptionUp(option{8})
    if(N:=O?,N=8):Print("option peer")
    M:=MapUp(map{1=>9})
    if(N:=M[1],N=9):Print("map peer")
    T:=TupleUp((10,"tag"))
    if(T(0)=10):Print("tuple peer {T(1)}")
