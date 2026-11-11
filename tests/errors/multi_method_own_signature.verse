# expect: signature
base := class:
    Pick(X:t where t:type)<transacts>:t = X|X
child := class(base):
    Pick<override>(X:[]u where u:type)<transacts>:u = X[0]|X[0]
Main():void = for(V:=child{}.Pick(array{7})): Print("{V}")
