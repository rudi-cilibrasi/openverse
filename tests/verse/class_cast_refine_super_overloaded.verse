pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
base := class:
    Ov(N:int):string = "int"
    Ov(S:string):string = "str"
holder := class(base):
    Get(P:pair(a, b) where a:type, b:type):string =
        if (D := dup[P]) then (super:)Ov(1) else "no"
Main():void = Print(holder{}.Get(dup(int){A := 1, B := 2}))
