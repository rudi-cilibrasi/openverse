# Variance of parametric interfaces, through an interface below them and a
# class that implements them (Book of Verse tests, ParametricTypes:
# InterfaceCovariantSubtyping and its siblings).
sup := class:
    Sup:int
sub := class(sup):
    Sub:int
source(t:type) := interface:
    Next():t
sink(t:type) := interface:
    Put(X:t):int
tagged(t:type) := interface:
    Tag():string
source2(t:type) := interface(source(t)):
sink2(t:type) := interface(sink(t)):
gen(t:type) := class(source2(t)):
    Item:t
    Next<override>():t = Item
taker(t:type) := class(sink2(t)):
    Put<override>(X:t):int = 7
label(t:type) := class(tagged(t)):
    Tag<override>():string = "label"
Main():void =
    S2:source2(sub) = gen(sub){Item := sub{Sup := 1, Sub := 2}}
    S:source(sup) = S2
    Print("covariant {S.Next().Sup}")
    if (B := sub[S.Next()]):
        Print("cast {B.Sub}")
    K2:sink2(sup) = taker(sup){}
    K:sink(sub) = K2
    Print("contravariant {K.Put(sub{Sup := 3, Sub := 4})}")
    L:tagged(int) = label(string){}
    Print("bivariant {L.Tag()}")
