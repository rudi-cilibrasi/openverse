# expect: in a method, it cannot call (super:) yet
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
base := class:
    Name():string = "base"
holder := class(base):
    Name<override>():string = "holder"
    Get(P:pair(a, b), X:a where a:type, b:type):b =
        if (D := dup[P]):
            Print((super:)Name())
            X
        else:
            P.B
Main():void = Print("{holder{}.Get(dup(int){A := 1, B := 2}, 3)}")
