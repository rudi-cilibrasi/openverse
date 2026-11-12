# Ordinary, generic and callable argument packing (#501).
First(P:tuple(int,string))<computes>:string=P(1)
Unit(P:tuple())<computes>:int=7
One(P:tuple(int))<computes>:int=P(0)
Nested(P:tuple(int,tuple(string,int)))<computes>:string="{P(0)} {P(1)(0)} {P(1)(1)}"
Id(X:t where t:type)<computes>:t=X
Count(X:[]t where t:type)<computes>:int=X.Length
Context(P:tuple([]t,?t),?V:t where t:type)<computes>:string="{P(0).Length}"
Named(P:tuple(int,string),?B:int,?A:int=4)<computes>:string="{P(0)} {P(1)} {B} {A}"
animal:=class{}
dog:=class(animal){}
Main():void=
    Print(Context(array{},false,?V:=7))
    Print(First(3,"value"))
    Print("{Unit()} {Unit(())} {One(9)}")
    Print(Nested(4,("nested",5)))
    R:tuple(int,int)=Id(1,2)
    A:[]int=Id(3,4)
    E:[][]int=Id(array{},array{5})
    Print("{R(0)} {R(1)} {A.Length} {E.Length} {Id(8)}")
    Print("{Count(1,2)} {Count(array{3})} {Count((4,5))}")
    Print("{Count(dog{},animal{})} {Count(animal{},dog{})}")
    Print(Named(6,"named",?B:=7))
    F:type{_(:tuple(int,string))<computes>:string}=First
    U:type{_(:tuple())<computes>:int}=Unit
    O:type{_(:tuple(int))<computes>:int}=One
    C:type{_(:[]int)<computes>:int}=Count
    Print(F(8,"value"))
    Print("{U()} {O(10)} {C(11,12)}")
