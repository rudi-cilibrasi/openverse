pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
base := class:
    Ov(N:int):string = "int"
    Ov(S:string):string = "str"
    # ((super:)M is only in an override of M, the Book's rule: the methods
    # that call it are overloads of M that override these)
    Ov(P:pair(a, b) where a:type, b:type):string = "no"
holder := class(base):
    Ov<override>(P:pair(a, b) where a:type, b:type):string =
        if (D := dup[P]) then (super:)Ov(1) else "no"
Main():void = Print(holder{}.Ov(dup(int){A := 1, B := 2}))
