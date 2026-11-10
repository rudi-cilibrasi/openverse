# no copy where the default's body uses a name the class's scope has beyond the
# interface's: Help and Limit stay the global ones, as without copies (#53)
Help():int = 1
Limit:int = 1
container(t:type) := interface:
    Get():t
c2(t:type) := interface(container([]t)):
    V():t
    Get<override>():[]t = if (Help() + Limit > 2) then array{V(), V(), V()} else array{V()}
box(a:type) := class(c2(a)):
    X:a
    V<override>():a = X
    Help():int = 5
bl(a:type) := class(c2(a)):
    X:a
    Limit:int = 7
    V<override>():a = X
Main():void =
    B := box(int){X := 1}
    L := bl(int){X := 1}
    Print("{B.Get().Length} {L.Get().Length}")
