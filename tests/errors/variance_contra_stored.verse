# expect: store, a class below sink, holds it in its field Last
# A contravariant interface whose implementation keeps what it is given: the
# Book has store(entity) a sink(player), but the override reads Last at the
# reference's type argument in Verse Core (docs/research/variance.md).
entity := class:
    ID:int
player := class(entity):
    Name:string
sink(t:type) := interface:
    Put(X:t):void
store(t:type) := class(sink(t)):
    Last:t
    Put<override>(X:t):void = {}
Main():void =
    S:sink(player) = store(entity){Last := entity{ID := 1}}
    S.Put(player{ID := 2, Name := "p"})
