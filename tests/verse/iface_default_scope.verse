# a pinned interface's default elaborated for each class below it in the
# interface's own scope (#53): its free names (Help, Limit) are the globals,
# not the members of box named alike; its named parameter (Pre) and loop
# binder (Y) are named like box's fields; it calls (super:) container's
# default; a dispatch from container(u) reaches box's copy
Help():int = 100
Limit:int = 3
container(t:type) := interface:
    Get():t
    Sum(?Pre:int = 0):int = Pre + 1
c2(t:type) := interface(container([]t)):
    V():t
    Get<override>():[]t =
        for (Y := 1..Limit) { V() }
    Sum<override>(?Pre:int = 0):int =
        (super:)Sum(?Pre := Pre + Help()) + Limit
box(a:type) := class(c2(a)):
    X:a
    (box:)Limit:int = 9
    Pre:int = 50
    Y:int = 60
    (box:)Help():int = 1000
    V<override>():a = X
G(C:container(u) where u:type):u = C.Get()
S(C:container(u) where u:type):int = C.Sum(?Pre := 5)
Main():void =
    B := box(int){X := 1}
    Print("{B.Get().Length} {G(B).Length}")
    Print("{B.Sum(?Pre := 5)} {S(B)} {B.Sum()}")
    Print("{B.Limit} {B.Pre} {B.Y} {B.Help()}")
