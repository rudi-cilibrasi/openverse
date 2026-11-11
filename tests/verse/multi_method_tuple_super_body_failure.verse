# Tuple calls preserve instantiated parameter types and call boundaries (#448).
base(t:type) := class:
    Pick(X:t,Y:t)<transacts>:t =
        Print("root")
        X | Y
mid(u:type) := class(base(u)):
    Pick<override>(X:u,Y:u)<transacts>:u = (super:)Pick((X,Y))
Main()<transacts><decides>:void =
    for(V:=mid(int){}.Pick(1,2)):
        Print("body {V}")
        V<2