vehicle:=class<allocates>{var N:int=7}
car:=class<allocates>(vehicle){Name:string="precise"}
counter:=class<allocates>{var N:int=0}
left(v:subtype(vehicle)):=interface<computes>:
    Take(X:t,?Step:int=1 where t:subtype(vehicle))<transacts>:t
right(v:subtype(vehicle)):=interface<computes>:
    Take(X:t,?Step:int=2 where t:subtype(vehicle))<transacts>:t
base(v:subtype(vehicle)):=class<computes>(left(v),right(v)):
    (left:)Take<override>(X:u,?Step:int=1 where u:subtype(vehicle))<transacts>:u=(set X.N+=10+Step;X)
    (right:)Take<override>(X:u,?Step:int=2 where u:subtype(vehicle))<transacts>:u=(set X.N+=100+Step;X)
child(v:subtype(vehicle)):=class<computes>(base(v)):
    (left:)Take<override>(X:u,?Step:int=1 where u:subtype(vehicle))<transacts>:u=(set X.N+=20+Step;X)
Pick(B:child(a),C:counter where a:subtype(vehicle))<transacts>:child(a)=(set C.N+=1;B)
Use(B:child(a),X:t,C:counter where a:subtype(vehicle),t:subtype(vehicle))<transacts>:t=Pick(B,C).(left:)Take(X)
Other(B:child(a),X:t where a:subtype(vehicle),t:subtype(vehicle))<transacts>:t=B.(right:)Take(X)
Main()<transacts>:void=
    C:=car{}
    O:=counter{}
    B:=child(car){}
    R:=Use(B,C,O)
    Print("qualified {R.Name} {C.N} {O.N}")
    S:=Other(B,C)
    Print("inherited {S.Name} {C.N}")
    if(Use(B,C,O),false?)then Print("bad")else Print("rollback {C.N} {O.N}")
