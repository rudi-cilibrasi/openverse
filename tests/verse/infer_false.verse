# A `false` that gives a type parameter its type, where nothing else does,
# is a `logic`, as `X := false` is and as `Identity(true)` is at `logic`
# (Book of Verse ch. 2, "Type Parameters"): an argument of a function, of a
# method, of a constructor function and of a function with several values,
# a named argument and a default. Where another argument gives the type, it
# is that type's empty value.
Id(X:t where t:type):t = X
Pair(X:t, Y:u where t:type, u:type):tuple(t, u) = (X, Y)
Pick(?X:t where t:type):t = X
Default(?X:t = false where t:type):t = X
HasValue(X:?t, Y:t where t:type):int = if (X?) then 1 else 0
box(t:type) := class:
    V:t
    Wrap(X:u where u:type):u = X
MakeBox(X:t where t:type):box(t) = box(t){V := X}
Both(X:t, ?Z:u = false where t:type, u:type):t = X | X
Show(L:logic):string = if (L?) then "true" else "false"

Main():void =
    A := Id(false)
    B := Id(true)
    Print("{Show(A)} {Show(B)}")
    T := Pair(1, false)
    Print("{T(0)} {Show(T(1))}")
    C := Pick(?X := false)
    D := Default()
    Print("{Show(C)} {Show(D)}")
    Print("{HasValue(false, 1)}")
    E := MakeBox(false)
    F := box(int){V := 1}.Wrap(false)
    Print("{Show(E.V)} {Show(F)}")
    for (Y := Both(false)) do Print("several {Show(Y)}")
