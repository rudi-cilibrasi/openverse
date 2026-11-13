# Fields with accessors in interfaces, inherited; a field with storage that a
# class gives accessors (Book of Verse tests, InterfaceWithAccessors.versetest
# 24-40), read and set through the interface: the object's class decides.
named := interface:
    var Name<getter(GetName)><setter(SetName)>:string = external{}
    var Stored:string = "anon"
    GetName(:accessor)<transacts>:string = "<{Stored}>"
    SetName(:accessor, V:string)<transacts>:void = set Stored = V

person := class(named):
    var Age:int = 0

sized := interface:
    var Size:int = 1

fixed := class(sized):
    var Size<override><getter(GetSize)><setter(SetSize)>:int = external{}
    var Real:int = 10
    GetSize(:accessor)<transacts>:int = Real * 2
    SetSize(:accessor, V:int)<transacts>:void = set Real = V

loose := class(sized):
    var Extra:int = 0

ShowSize(S:sized)<transacts>:int = S.Size

Grow(S:sized)<transacts>:void =
    set S.Size += 1

Main()<transacts>:void =
    P := person{Name := "ada", Age := 36}
    Print(P.Name)
    N:named = P
    set N.Name = "grace"
    Print(N.Name)
    F := fixed{}
    L := loose{}
    Print("{ShowSize(F)} {ShowSize(L)}")
    Grow(F)
    Grow(L)
    Print("{ShowSize(F)} {ShowSize(L)} {F.Real}")
    for (S : array{F, L}):
        Print("{S.Size}")
