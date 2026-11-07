# expect: 4:0: F is defined twice with parameters a call cannot tell apart, (age) and (int): overloads must take disjoint types
age := type{_X:int where 0 <= _X, _X <= 120}
F(A:age):int = 1
F(A:int):int = 2
Main():void = Print("x")
