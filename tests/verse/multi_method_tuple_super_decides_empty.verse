# Tuple calls preserve instantiated parameter types and call boundaries (#448).
base(t:type) := class:
    Pick(X:t,Y:t,Ok:logic)<transacts><decides>:t =
        Ok?
        X | Y
mid(u:type) := class(base(u)):
    Pick<override>(X:u,Y:u,Ok:logic)<transacts><decides>:u = (super:)Pick[(X,Y,Ok)]
Main()<transacts>:void =
    for(V:=mid(int){}.Pick[1,2,true]){Print("{V}")}
    for(V:=mid(int){}.Pick[1,2,false]){Print("bad")}
    Print("end")