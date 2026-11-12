# Receiver-free packing through direct, inherited, dynamic and qualified calls.
i := interface:
    Pair(P:tuple(int,string),?N:int=2):string
base := class(i):
    Seed:int=10
    Pair<override>(P:tuple(int,string),?N:int=Seed):string="base {P(0)} {P(1)} {N}"
    Unit(P:tuple()):int=Seed
    One(P:tuple(int)):int=P(0)+Seed
    Count(P:[]t where t:type):int=P.Length
    Pass(P:t where t:type):t=P
sub := class(base):
    Seed<override>:int=20
    Pair<override>(P:tuple(int,string),?N:int=Seed):string="sub {P(0)} {P(1)} {N}"
    Parent():string=(super:)Pair(1,"super")
Run(X:base):void=
    Print(X.Pair(2,"dynamic"))
    Print("{X.Unit()} {X.One(3)} {X.Count(4,5)}")
    A:[]int=X.Pass(6,7)
    Print("{A.Length}")
box(t:type):=class:
    Value:t
MakeBox<constructor>(P:tuple(t,t) where t:type):=box(t):
    Value:=P(1)
Main():void=
    X:=sub{}
    Print(X.Pair(8,"direct",?N:=9))
    Print(X.Parent())
    Run(X)
    I:i=X
    Print(I.Pair(10,"interface"))
    Print(X.(i:)Pair(11,"qualified"))
    B:=MakeBox(12,13)
    Print("{B.Value}")
