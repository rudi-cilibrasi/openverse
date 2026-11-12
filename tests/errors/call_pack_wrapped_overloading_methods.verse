# expect: loud has overloads of Show a call cannot tell apart
# overloaded methods (Book of Verse ch. 6): in an interface, a class and a
# subclass that overrides one overload and adds another; bare calls, (super:)
# and dispatch through the interface

printer := interface:
    Show(X:int):string
    Show(S:string):string

base := class(printer):
    Show<override>(X:int):string = "int {X}"
    Show<override>(S:string):string = "string {S}"
    Twice(X:int):string = Show(X) + " " + Show("{X}")

loud := class(base):
    Show<override>(S:string):string = "LOUD {(super:)Show(S)}"
    Show(C:char):string = "char"

Main():void =
    B := base{}
    Print(B.Show(1))
    Print(B.Show("a"))
    Print(B.Twice(2))
    L := loud{}
    Print(L.Show(3))
    Print(L.Show("b"))
    Print(L.Show('z'))
    P:printer = loud{}
    Print(P.Show("c"))
    Ps:[]printer = array{base{}, loud{}}
    for (Q : Ps) { Print(Q.Show("d")) }
