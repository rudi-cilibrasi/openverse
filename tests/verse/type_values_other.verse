# Metatypes of types that are not classes (Book of Verse tests, Subtype.versetest
# 113-119, 140-142; TypeParam.versetest 3-16), and concrete_subtype(any) and
# concrete_subtype(comparable) (MetatypeConcreteSubtype.versetest 12-35).
color := enum{Red, Green}
point := struct:
    X:int = 0
item := class<unique><concrete>:
    N:int = 1
plain := class<concrete>:
    M:int = 2
holder := class:
    Kind:subtype(int)
    Shape:subtype([]item)
    Maybe:subtype(?item)
    Colour:subtype(color)
Identity(X:t where t:type):t = X
Describe(T:type):string = "a type"
Main():void =
    A:type = Identity(int)
    B:type = Identity(point)
    C:type = color
    Print(Describe(A))
    U:concrete_subtype(comparable) = item
    V:concrete_subtype(any) = plain
    W:[]concrete_subtype(any) = array{}
    Print(ToString(W.Length))
