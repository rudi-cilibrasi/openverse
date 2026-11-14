# Omitted defaults infer independent method types at a static implementation.
DefaultInt()<transacts>:int =
    Print("root default")
    7
DefaultString()<transacts>:string =
    Print("child default")
    "s"
root(a:type) := class:
    Value:a
    var Count:int=0
    Pick(?X:t=DefaultInt(),?Y:u=8 where t:type,u:type)<transacts>:tuple(a,t,u) =
        set Count+=1
        (Value,X,Y)|(Value,X,Y)
    Discard(?X:t=DefaultInt() where t:type)<transacts>:int = 1|2
child(b:type) := class(root(b)):
    Pick<override>(?X:v=DefaultString(),?Y:w=9 where v:type,w:type)<transacts>:tuple(b,v,w) =
        set Count+=1
        (Value,X,Y)|(Value,X,Y)
    Discard<override>(?X:v=DefaultString() where v:type)<transacts>:int = 3|4
leaf(c:type) := class(child(c)) {}
animal(t:type) := class { Data:t }
dog(t:type) := class(animal(t)) { Code:int }
factory := class:
    Make(?X:t=DefaultInt() where t:type)<transacts>:animal(t) =
        animal(t){Data:=X}|animal(t){Data:=X}
kennel := class(factory):
    Make<override>(?X:u=DefaultString() where u:type)<transacts>:dog(u) =
        dog(u){Data:=X,Code:=1}|dog(u){Data:=X,Code:=2}
iroot(a:type) := interface:
    Implied(?X:t=DefaultInt() where t:type)<transacts>:t = X|X
iextra(b:type,c:type) := class(iroot(b)):
    Implied<override>(?X:u=DefaultString() where u:type)<transacts>:u = X|X
holder(x:type,y:type) := class(iextra(x,y)) {}
All(C:leaf(z) where z:type):[]tuple(z,string,int) = for(V:=C.Pick()): V
IfaceAll(H:holder(z,w) where z:type,w:type):[]string = for(V:=H.Implied()): V
Main():void =
    C:=leaf(int){Value:=5}
    for(V:All(C)): Print("all {V(0)} {V(1)} {V(2)}")
    if(V:=first{C.Pick()})then Print("first {V(0)} {V(1)} {V(2)}")
    if(V:=C.Pick(),false?)then Print("unreachable")
    Print("count {C.Count}")
    for(V:=C.Discard()): Print("discard {V}")
    for(D:=kennel{}.Make()): Print("dog {D.Data} {D.Code}")
    for(V:IfaceAll(holder(int,string){})): Print("interface {V}")
