# Disjoint flattened domains across inherited generic interfaces, defaults
# and generic constructors. One tuple argument can reach the other overload.
i(t:type) := interface:
    M(P:tuple(int,t),?N:int=0):string
    M(X:string,Y:string,?N:int=0):string
base(t:type) := class(i(t)):
    M<override>(P:tuple(int,t),?N:int=0):string = "base {P(0)} {N}"
    M<override>(X:string,Y:string,?N:int=0):string = "strings {X}{Y} {N}"
low(t:type) := class(base(t)):
    M<override>(P:tuple(int,t),?N:int=0):string = "low {P(0)} {N}"
out := class:
    Label:string
Make<constructor>(P:tuple(int,t) where t:type) := out:
    Label := "tuple {P(0)}"
Make<constructor>(X:string,Y:string) := out:
    Label := "strings {X}{Y}"
F(P:tuple(int,t),?N:int=0 where t:type):string = "tuple {P(0)} {N}"
F(X:string,Y:string,?N:int=0):string = "strings {X}{Y} {N}"
Main():void =
    I:i(int) = low(int){}
    Print(I.M((1,2)))
    Print(I.M("a","b"))
    Print(I.M(("c","d"),?N:=7))
    Print(Make((3,4)).Label)
    Print(Make("e","f").Label)
    Print(Make(("g","h")).Label)
    Print(F((5,6),?N:=8))
    Print(F("i","j",?N:=9))
    Print(F(("k","l"),?N:=10))
