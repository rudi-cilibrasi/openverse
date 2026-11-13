# Covariant multi-value calls preserve static results and consumer boundaries (#283).
animal(t:type) := class { V:t; Label():string="animal" }
dog(t:type) := class(animal(t)) { Bark:int=0; Label<override>():string="dog" }
maker(a:type,b:type) := class:
    Get(X:a,Y:[]b,?K:int=0)<transacts>:animal(a) = animal(a){V:=X} | animal(a){V:=X}
fixed(u:type) := class(maker(int,u)):
    Get<override>(X:int,Y:[]u,?K:int=0)<transacts>:dog(int) = dog(int){V:=X,Bark:=10+K} | dog(int){V:=X,Bark:=11+K}
repeated(t:type) := class(maker(t,t)):
    Get<override>(X:t,Y:[]t,?K:int=0)<transacts>:dog(t) = dog(t){V:=X,Bark:=20+K} | dog(t){V:=X,Bark:=21+K}
extra(a:subtype(comparable),b:subtype(comparable),w:subtype(comparable)) := class(maker(a,b)):
    E:w
    Get<override>(X:a,Y:[]b,?K:int=0)<transacts>:dog(a) = if(E=E) then (dog(a){V:=X,Bark:=30+K} | dog(a){V:=X,Bark:=31+K}) else dog(a){V:=X}
reorder(x:type,y:type) := class(maker(y,x)):
    Get<override>(X:y,Y:[]x,?K:int=0)<transacts>:dog(y) = dog(y){V:=X,Bark:=40+K} | dog(y){V:=X,Bark:=41+K}
Base(P:maker(a,b),V:a where a:type,b:type)<transacts>:[]animal(a) = for(R:=P.Get(V,array{})){R}
Main()<transacts>:void =
    for(D:=fixed(string){}.Get((7,array{}))){Print("f {D.Bark}")}
    for(D:=repeated(int){}.Get((3,array{}))){Print("r {D.Bark}")}
    E:=extra(int,string,int){E:=1}
    for(D:=E.Get((8,array{}))){Print("e {D.Bark}")}
    for(D:=reorder(string,int){}.Get((9,array{}))){Print("p {D.Bark}")}
    for(A:Base(E,8)){Print("base {A.V} {A.Label()}")}
    for(A:Base(maker(int,string){},2)){Print("base {A.V} {A.Label()}")}
