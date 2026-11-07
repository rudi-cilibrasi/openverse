# unique classes at related class arguments compare (#116 review: not refused)
I1 := interface:
    M1():int
I2 := interface:
    M2():int
base := class<unique>:
    V:int = 0
sub := class<unique>(base):
    W:int = 0
other := class<unique>:
    V:int = 0
cboth := class<unique>(I1, I2):
    M1<override>():int = 1
    M2<override>():int = 2
c1 := class<unique>(I1):
    M1<override>():int = 1
d1 := class<unique>(c1, I2):
    M2<override>():int = 2
E := enum{A, B}
F := enum{A, B}
box(t:type) := struct:
    V:t
pt := struct:
    X:int = 0
Main():void =
    Cb := cboth{}
    D := d1{}
    S := sub{}
    X:base = S; if (box(base){V := X} = box(sub){V := S}) then Print("eq") else Print("ne")
