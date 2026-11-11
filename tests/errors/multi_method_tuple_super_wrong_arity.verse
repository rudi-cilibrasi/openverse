# expect: expected tuple(int, int), found tuple(int, int, int)
base(t:type) := class:
    Pick(X:t,Y:t):int = 1 | 2
mid(u:type) := class(base(u)):
    Pick<override>(X:u,Y:u):int = (super:)Pick((X,Y,X))
Main():void = for(N:=mid(int){}.Pick(1,2)){Print("{N}")}