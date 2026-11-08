# expect: ia has more Verse Core type arguments than box (a class between them has type parameters of its own), so it cannot override Name
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
