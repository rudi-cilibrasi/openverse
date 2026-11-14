# A class's field of a concrete_subtype constructs in its methods (Book of
# Verse ch. 11, "concrete_subtype": "The type value has to be held in a class
# *field*"; its tests, MetatypeConcreteSubtype.versetest 211-263).
thing := class<abstract>:
    Value:comparable
    Name():string
every_thing := class<concrete>(thing):
    Value<override>:int = 42
    Name<override>():string = "every"
no_thing := class<concrete>(thing):
    Value<override>:logic = false
    Name<override>():string = "no"
maker := class:
    ThingType:concrete_subtype(thing)
    MakeIt():thing = ThingType{}
Main():void =
    A := maker{ThingType := every_thing}.MakeIt()
    B := maker{ThingType := no_thing}.MakeIt()
    Print("{A.Name()} {if (A.Value = 42) then "42" else "?"} {B.Name()} {if (B.Value = false) then "false" else "?"}")
