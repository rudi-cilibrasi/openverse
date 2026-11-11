# Tuple calls preserve instantiated parameter types and call boundaries (#448).
base(t:type) := class:
    Pick(X:t,Y:[]t):int = Y.Length | Y.Length+1
mid(u:type) := class(base(u)):
    Pick<override>(X:u,Y:[]u):int =
        T:= (X,Y)
        (super:)Pick(T)
Main():void = for(N:=mid(string){}.Pick("s",array{"x"})){Print("{N}")}