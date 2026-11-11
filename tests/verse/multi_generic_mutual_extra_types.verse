# A member can have extra type parameters determined only by its arguments.
leaf(t:type) := struct { E:[]t=Concatenate() }
A(X:t,N:int where t:type)<transacts><decides>:tuple(t,int) =
    N>=0
    Print("A {N}")
    (X,N) | B[option{X},X,N-1]
B(Extra:u,X:v,N:int,?E:[]u=Concatenate() where u:type,v:type)<transacts><decides>:tuple(v,int) =
    N>=0
    T:?u=false
    L:leaf(u)=leaf{}
    Print("B {N} {E.Length} {L.E.Length}")
    (X,N) | A[X,N-1]
Pick(X:a,W:w where a:type,w:type)<transacts>:?a =
    option{V:=A[X,2],E:[]w=Concatenate(),V(1)=0,V(0)}
pair(a:type,b:type) := class { First:a; Second:b }
dup(t:type) := class(pair(t,t)) {}
Refined(P:pair(a,b) where a:type,b:type):void =
    if(D:=dup[P]):
        for(V:=A[D.First,1]): Print("refined {V(1)}")
root := class {}
hidden(t:type) := class(root) { Value:t }
Opened(P:root):void =
    if(H:=hidden[P]):
        if(V:=A[H.Value,1],V(1)=0)then Print("opened {V(1)}")
Main():void =
    for(V:=A[7,2]): Print("got {V(0)} {V(1)}")
    if(V:=Pick("s",option{7})?)then Print("first {V}")
    Refined(dup(int){First:=1,Second:=2})
    Refined(dup(string){First:="a",Second:="b"})
    Opened(hidden(int){Value:=7})
    Opened(hidden(string){Value:="s"})
