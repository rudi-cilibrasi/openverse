# one field declared by two interfaces, as the type parameter in one and as
# int in the other, in classes that fix the parameter to int: read and set
# through either interface, and through a class whose subclass takes the
# field from the other interface (#205)
x(t:type) := interface:
    var F:t
y(t:type) := interface:
    var F:int
c := class(x(int), y(int)):
    G:int = 0
e(t:type) := class(y(t)):
    H:int = 0
# (a class that fixes t and takes F from y alone)
f := class(y(int)):
    J:int = 0
b(t:type) := class(y(t)):
    K:int = 0
d := class(b(int), x(int)):
    L:int = 0
g := class(b(int)):
    M:int = 0
Fx(N:x(t) where t:type):t = N.F
Fy(N:y(t) where t:type):int = N.F
Fb(B:b(t) where t:type):int = B.F
Sx(N:x(t), V:t where t:type):void =
    set N.F = V
Sy(N:y(t), V:int where t:type):void =
    set N.F = V
Sb(B:b(t), V:int where t:type):void =
    set B.F = V
Main():void =
    C := c{F := 1}
    E := e(string){F := 2}
    Print("{C.F} {Fx(C)} {Fy(C)} {Fy(E)}")
    Sy(C, 5)
    Sy(E, 6)
    Print("{Fx(C)} {Fy(E)}")
    Sx(C, 7)
    Print("{Fy(C)}")
    D := d{F := 1}
    Print("{Fb(D)} {Fx(D)} {Fy(D)} {Fb(b(string){F := 4})}")
    Sb(D, 2)
    Print("{D.F}")
    Sx(D, 3)
    Print("{Fb(D)} {D.F}")
    Fv := f{F := 8}
    G := g{F := 9}
    Sy(Fv, 10)
    Sb(G, 11)
    Print("{Fy(Fv)} {Fb(G)} {Fy(G)}")
