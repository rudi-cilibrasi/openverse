# expect: mid.Pick must have the signature of base.Pick, which it overrides
base(t:type) := class:
    Pick(X:t,Y:t):int = 1 | 2
mid(u:type) := class(base(int)):
    Pick<override>(X:string,Y:string):int = (super:)Pick((X,Y))
Main():void = for(N:=mid(int){}.Pick("s","t")){Print("{N}")}