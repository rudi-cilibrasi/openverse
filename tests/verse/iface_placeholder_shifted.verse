# interface fields that every class has at one place, not the interface's
# own: read and set there directly, placeholders laid out to match (#157)
named(t:type) := interface:
    Name:string
    Get():t
pre(t:type) := class:
    P:int = 0
ni := class(pre(int), named(int)):
    Get<override>():int = P
NameOf(N:named(t) where t:type):string = N.Name
# every class lists `b` first, so `B` sits at 0 below `n`, at 1 in `n`
a(t:type) := interface:
    var A:int
b(t:type) := interface:
    var B:int
n(t:type) := interface(a(t), b(t)):
    Get():t
c := class(b(int), n(int)):
    Get<override>():int = A * 10 + B
d := class(b(string), n(string)):
    Get<override>():string = "{A}{B}"
BN(N:n(t) where t:type):int = N.B
SetB(Ns:[]n(t), X:int where t:type):void =
    for (N : Ns):
        set N.B = X
# `F` is declared above `m`: `m`'s classes agree on its place, `top`'s not
top(t:type) := interface:
    var F:int
m(t:type) := interface(top(t)):
    G:int
    Get():t
other(t:type) := class(pre(t), top(t)):
    Y:int = 0
m1 := class(m(int)):
    Get<override>():int = F + G
m2 := class(m(string)):
    Get<override>():string = "s{F}"
Fs(Ms:[]m(t) where t:type):[]int = for (M : Ms) { M.F }
Bump(Ms:[]m(t) where t:type):void =
    for (M : Ms):
        set M.F = M.F + 10
TopF(T:top(t) where t:type):int = T.F
# an interface at a type argument that is the interface itself: the
# placeholder of `slot(slot(u))` holds one of `slot(u)`
slot(t:type) := interface:
    var Item:t
    Show():string
islot := class(slot(int)):
    Show<override>():string = "i{Item}"
sslot := class(slot(slot(int))):
    Show<override>():string = "s({Item.Show()})"
Shows(Ss:[]slot(t) where t:type):[]string = for (S : Ss) { S.Show() }
Inner(Ss:[]slot(slot(u)) where u:type):[]string = for (S : Ss) { S.Item.Show() }
Main():void =
    Print(NameOf(ni{Name := "n"}))
    C := c{A := 1, B := 2}
    Print("{BN(C)} {C.Get()}")
    SetB(array{C}, 5)
    Print("{BN(C)} {C.Get()} {BN(d{A := 3, B := 4})}")
    M := m1{F := 1, G := 2}
    Bump(array{M})
    for (X : Fs(array{M})) { Print("{X}") }
    for (X : Fs(array{m2{F := 5, G := 0}})) { Print("{X}") }
    Print("{TopF(other(int){F := 7})} {TopF(M)} {M.Get()}")
    I := islot{Item := 1}
    for (X : Shows(array{sslot{Item := I}})) { Print(X) }
    for (X : Shows(array{I})) { Print(X) }
    for (X : Inner(array{sslot{Item := I}})) { Print(X) }
