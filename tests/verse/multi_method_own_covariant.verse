# Static result selection substitutes class and method arguments together.
animal(a:type,b:type) := class { First:a; Second:b }
dog(a:type,b:type) := class(animal(a,b)) { Code:int }
factory(a:type) := class:
    Value:a
    Make(X:b where b:type)<transacts>:animal(a,b) =
        animal(a,b){First:=Value,Second:=X}|animal(a,b){First:=Value,Second:=X}
kennel(u:type) := class(factory(u)):
    Make<override>(X:v where v:type)<transacts>:dog(u,v) =
        dog(u,v){First:=Value,Second:=X,Code:=1}|dog(u,v){First:=Value,Second:=X,Code:=2}
Run(B:kennel(v),X:u where u:type,v:type):[]tuple(v,u,int) =
    for(D:=B.Make(X)): (D.First,D.Second,D.Code)
Main():void =
    for(V:Run(kennel(int){Value:=7},"s")): Print("{V(0)} {V(1)} {V(2)}")
    B:factory(string)=kennel(string){Value:="a"}
    for(D:=B.Make(7)): Print("base {D.First} {D.Second}")
