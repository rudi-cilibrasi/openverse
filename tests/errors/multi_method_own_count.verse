# expect: type parameter(s) of its own
base := class:
    Pick(X:t where t:type)<transacts>:t = X|X
child := class(base):
    Pick<override>(X:int)<transacts>:int = X|X
Main():void = for(V:=child{}.Pick(7)): Print("{V}")
