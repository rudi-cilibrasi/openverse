# A lazy first-success helper captures the source receiver for scalar super.
base(t:type) := class:
    Data:t
    Offset:int
    var Count:int=0
    Read(N:int,?E:[]t=Concatenate())<transacts>:int =
        set Count+=1
        Print("read {N} {E.Length}")
        Offset+N
child(u:type) := class(base(u)):
    Walk(N:int)<transacts><decides>:int =
        N>=0
        Print("visit {N}")
        (super:)Read(N)|Self.Walk[N-1]
First(C:child(a),N:int,W:w where a:type,w:type):?int =
    option{V:=C.Walk[3]; E:[]w=Concatenate(); V=N; V}
Main():void =
    C:=child(string){Data:="s",Offset:=10}
    if(V:=First(C,11,option{7})?)then Print("first {V}")
    Print("count {C.Count}")
    if(V:=First(C,99,7)?)then Print("unreachable")else Print("none")
    Print("count {C.Count}")
    for(V:=C.Walk[1]): Print("all {V}")
    Print("count {C.Count}")
