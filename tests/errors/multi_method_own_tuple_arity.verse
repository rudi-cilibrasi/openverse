# expect: expected tuple
base := class:
    Pick(X:t,Y:t where t:type)<transacts>:t = X|Y
child := class(base):
    Pick<override>(X:u,Y:u where u:type)<transacts>:u = Y|X
Main():void = for(V:=child{}.Pick((1,2,3))): Print("{V}")
