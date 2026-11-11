box(t:type) := class:
    V:t
    var Count:int=0
    Left(N:int,Step:int)<transacts><decides>:tuple(t,int) =
        N>=0
        set Count+=1
        Print("left {N}")
        (V,Step) | Self.Right[(N-1,Step+1)]
    Right(N:int,Step:int,?E:[]t=array{V})<transacts><decides>:tuple(t,int) =
        N>=0
        set Count+=1
        Print("right {N} {E.Length}")
        T:tuple(t,int)=(V,Step)
        T | Self.Left[(N-1,Step+1)]
Main():void =
    I:=box(int){V:=7}
    for(V:=I.Left[(2,0)],V(1)>0): Print("got {V(0)} {V(1)}")
    Print("count {I.Count}")
    S:=box(string){V:="s"}
    if(V:=S.Right[(2,0)],V(1)=2)then Print("first {V(0)} {V(1)}")
    Print("count {S.Count}")
