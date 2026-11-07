# expect: 3:0: F is defined twice with parameters a call cannot tell apart, (int) and (rational): overloads must take disjoint types
F(X:int):int = 1
F(X:rational):int = 2
Main():void = Print("{F(1)}")
