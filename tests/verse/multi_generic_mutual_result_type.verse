# The other member's type comes only from its result, including in a default.
leaf(t:type) := struct { E:[]t=Concatenate() }
A(X:t,N:int where t:type)<transacts>:[]t =
    Print("A {N}")
    if(N>0)then(array{X}|B(N-1))else array{X}
B(N:int,?K:int=leaf(u){}.E.Length where u:type)<transacts>:[]u =
    Print("B {N} {K}")
    if(N>0)then(array{}|A(Err(),N-1))else array{}
root := class {}
hidden(t:type) := class(root) { Value:t }
Opened(P:root):void =
    if(H:=hidden[P]):
        if(V:=A(H.Value,2),V.Length=0)then Print("opened")
Main():void =
    for(V:=A(7,1)): Print("all {V.Length}")
    if(V:=A("s",2),V.Length=0)then Print("empty")
    if(V:=A("s",1),V.Length>2)then Print("unexpected")else Print("none")
    Opened(hidden(int){Value:=7})
    Opened(hidden(string){Value:="s"})
