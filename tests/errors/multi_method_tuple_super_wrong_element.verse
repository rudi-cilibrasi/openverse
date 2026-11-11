# expect: expected tuple(string, int), found tuple(int, string)
base(a:type,b:type) := class:
    Pick(X:a,Y:b):int = 1 | 2
mid(x:type,y:type) := class(base(y,x)):
    Pick<override>(X:y,Y:x):int = (super:)Pick((Y,X))
Main():void = for(N:=mid(int,string){}.Pick("s",7)){Print("{N}")}