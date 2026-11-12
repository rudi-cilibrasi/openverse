# expect: call cannot tell apart
a := class{}
F(X:tuple(a),Y:a):int = 1
F(X:[int]a,Y:a):int = 2
Main():void = {}
