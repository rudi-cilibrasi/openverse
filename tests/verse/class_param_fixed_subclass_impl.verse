# regression test from the #53 re-review (q52)
shape(t:type) := class<abstract>:
    Area():int
sq(t:type) := class(shape(t)):
    Area<override>():int = 4
intsq := class(sq(int)):
    N:int = 0
Main():void = Print("{intsq{}.Area()}")
