# expect: the parameter 'X' of F has the name of the constant X (2:0): Verse does not allow shadowing (Book of Verse ch. 10); rename one, or qualify this one, (local:)X
X:int = 1
F(X:int):int = X
Main():void = {}
