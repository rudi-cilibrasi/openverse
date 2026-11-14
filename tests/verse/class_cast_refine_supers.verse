# Refining casts' branches in methods calling (super:) (#243): at the refined object's values, nested in its
# own arguments, through a chain of three classes, an interface's default, in a void method
# ((super:)M only in an override of M, the Book's rule: each method that calls it is an overload of M)
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
named := interface:
    Tag(N:int):string = "named{N}"
    Tag(P:pair(a, b) where a:type, b:type):void = {}
base := class(named):
    Name(N:int):string = "base{N}"
    Twice(N:int):int = N * 2
    Name(P:pair(a, b), X:a where a:type, b:type):b = P.B
    Twice(P:pair(a, b) where a:type, b:type):void = {}
    Name(P:pair(a, b) where a:type, b:type)<transacts>:void = {}
mid := class(base):
    Name<override>(N:int):string = "mid{N}"
    Twice<override>(N:int):int = N * 3
top := class(mid):
    Name<override>(N:int):string = "top{N}"
    Tag<override>(N:int):string = "top-tag"
    Name<override>(P:pair(a, b), X:a where a:type, b:type):b =
        if (D := dup[P]):
            Print((super:)Name(D.C))
            X
        else:
            P.B
    Twice<override>(P:pair(a, b) where a:type, b:type):void =
        if (D := dup[P]):
            Print("{(super:)Twice((super:)Twice(D.C))}")
    Tag<override>(P:pair(a, b) where a:type, b:type):void =
        if (D := dup[P]):
            Print((super:)Tag(D.C + 1))
    Name<override>(P:pair(a, b) where a:type, b:type)<transacts>:void =
        if (D := dup[P]):
            Print((super:)Name(100))
Main()<transacts>:void =
    T := top{}
    D := dup(int){A := 1, B := 2, C := 4}
    R := T.Name(D, 3)
    T.Twice(D)
    T.Tag(D)
    Print("{R}")
    Print("{T.Name(pair(int, string){A := 1, B := "x"}, 3)}")
    T.Name(dup(int){A := 1, B := 2})
