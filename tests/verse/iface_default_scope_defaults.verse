# the named parameters' defaults of a pinned interface's default resolve in the
# interface's scope too (#53): Help, Limit and (super:)Base in c2's defaults
# mean what they do in c2, not box's members named alike (nor closed's Limit, of
# another type), on direct calls and through c2(u); container(u) reaches the copy
Help():int = 100
Limit:int = 3
container(t:type) := interface:
    Get():t
    Base():int = 1
    Sum(?Pre:int = 0):int
    Lim(?Pre:int = 0):int
    Sup(?Pre:int = 0):int
c2(t:type) := interface(container([]t)):
    V():t
    Get<override>():[]t = array{V()}
    Base<override>():int = 20
    Sum<override>(?Pre:int = Help()):int = Pre
    Lim<override>(?Pre:int = Limit):int = Pre
    Sup<override>(?Pre:int = (super:)Base()):int = Pre
box(a:type) := class(c2(a)):
    X:a
    (box:)Limit:int = 9
    (box:)Help():int = 1000
    V<override>():a = X
closed := class(c2(int)):
    (closed:)Limit:string = "nine"
    V<override>():int = 5
S(C:c2(u) where u:type):string = "{C.Sum()} {C.Lim()} {C.Sup()}"
K(C:container(u) where u:type):int = C.Sum(?Pre := 5)
Main():void =
    B := box(int){X := 1}
    L := closed{}
    Print("box: {B.Sum()} {B.Lim()} {B.Sup()} | {S(B)} | {K(B)}")
    Print("closed: {L.Sum()} {L.Lim()} {L.Sup()} | {S(L)} | {K(L)}")
    Print("{B.Limit} {B.Help()} {L.Limit}")
