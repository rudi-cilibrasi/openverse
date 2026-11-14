# An inherited interface default retains class, opened and method arguments.
root(t:type) := interface:
    Read():t
    Tag():int
    Both(X:u,?Y:u=X,?E:[]u=Concatenate() where u:type)<transacts>:tuple(t,u,int) =
        Print("default {Tag()}")
        (Read(),X,Tag())|(Read(),Y,Tag()+1)
extra(a:type,b:type) := class<abstract>(root(a)):
    Both<override>(X:v,?Y:v=X,?E:[]v=Concatenate() where v:type)<transacts>:tuple(a,v,int) =
        (Read(),Y,99)|(super:)Both(X,?Y:=Y)
holder(a:type,b:type) := class(extra(a,b)):
    Store:a
    Extra:b
    Read<override>():a=Store
    Tag<override>():int=3
Get(B:root(u),X:t,Y:t where t:type,u:type):[]tuple(u,t,int) =
    for(V:=B.Both(X,?Y:=Y)): V
Main():void =
    B:root(int)=holder(int,string){Store:=7,Extra:="hidden"}
    for(V:=B.Both("x",?Y:="y")): Print("all {V(0)} {V(1)} {V(2)}")
    if(V:=B.Both("x",?Y:="y"),V(2)=3)then Print("first {V(0)} {V(1)}")
    if(V:=B.Both("x",?Y:="y"),V(2)<0)then Print("unexpected")else Print("none")
    for(V:Get(B,"p","q")): Print("generic {V(0)} {V(1)} {V(2)}")
