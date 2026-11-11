# Type names can change in overrides and super tuples retain their scope.
base(t:type) := class:
    Value:t
    Pick(X:u,Y:u,?E:[]u=Concatenate() where u:type)<transacts>:tuple(t,u) =
        Print("base {E.Length}")
        (Value,X)|(Value,Y)
child(a:type) := class(base(a)):
    Pick<override>(X:b,Y:b,?E:[]b=array{X} where b:type)<transacts>:tuple(a,b) =
        Print("child {E.Length}")
        (Value,Y)|(super:)Pick((X,Y))
Run(B:base(b),X:a,Y:a where a:type,b:type):[]tuple(b,a) =
    for(V:=B.Pick((X,Y))): V
Main():void =
    B:base(int)=child(int){Value:=7}
    for(V:Run(B,"x","y")): Print("got {V(0)} {V(1)}")
    for(V:=B.Pick(("p","q"))): Print("direct {V(1)}")
    if(V:=B.Pick(("x","y")),V(1)="x")then Print("first {V(0)} {V(1)}")
    if(V:=B.Pick(("x","y")),V(1)="z")then Print("unexpected")else Print("none")
