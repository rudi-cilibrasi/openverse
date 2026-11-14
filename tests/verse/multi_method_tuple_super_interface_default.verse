# Tuple calls preserve instantiated parameter types and call boundaries (#448).
base(t:type) := interface:
    Pick(X:t,Y:t)<transacts>:t = X | Y
mid(u:type) := class(base(u)):
    Pick<override>(X:u,Y:u)<transacts>:u = (super:)Pick((Y,X))
leaf(v:type) := class(mid(v)) {}
Main()<transacts>:void = for(N:=leaf(int){}.Pick(1,2)){Print("{N}")}