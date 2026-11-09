# a class below one with a type parameter of its own fixes it and overrides:
# a dispatch on box opens it (#209)
box(t:type) := class:
    V:t
    Name():string = "box"
arrbox(u:type) := class(box([]u)):
    W:int = 0
ia := class(arrbox(int)):
    Name<override>():string = "ia"
N(B:box(t) where t:type):string = B.Name()
Main():void =
    Print(N(ia{V := array{1}}))
    Print(N(box(int){V := 2}))
    Print(N(arrbox(string){V := array{}}))
