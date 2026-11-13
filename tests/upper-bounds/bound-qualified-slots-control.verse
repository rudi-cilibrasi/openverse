vehicle:=class<allocates>{var N:int=7}
car:=class<allocates>(vehicle){Name:string="precise"}
counter:=class<allocates>{var N:int=0}
left(v:type):=interface<computes>:
    Take(X:car,?Step:int=1)<transacts>:car
right(v:type):=interface<computes>:
    Take(X:car,?Step:int=2)<transacts>:car
base(v:type):=class<computes>(left(v),right(v)):
    (left:)Take<override>(X:car,?Step:int=1)<transacts>:car=(set X.N+=10+Step;X)
    (right:)Take<override>(X:car,?Step:int=2)<transacts>:car=(set X.N+=100+Step;X)
child(v:type):=class<computes>(base(v)):
    (left:)Take<override>(X:car,?Step:int=1)<transacts>:car=(set X.N+=20+Step;X)
Pick(B:child(a),C:counter where a:type)<transacts>:child(a)=(set C.N+=1;B)
Use(B:child(a),X:car,C:counter where a:type)<transacts>:car=Pick(B,C).(left:)Take(X)
Other(B:child(a),X:car where a:type)<transacts>:car=B.(right:)Take(X)
Main()<transacts>:void=
    C:=car{}
    O:=counter{}
    B:=child(car){}
    R:=Use(B,C,O)
    Print("qualified {R.Name} {C.N} {O.N}")
    S:=Other(B,C)
    Print("inherited {S.Name} {C.N}")
    if(Use(B,C,O),false?)then Print("bad")else Print("rollback {C.N} {O.N}")
