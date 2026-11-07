# regression test from the #53 re-review (q53)
shape(t:type) := class<abstract>:
    Area():int
sq(t:type) := class(shape(t)):
    Area<override>():int = 4
tagged(t:type, n:type) := class(sq(t)):
    Tag:n
Main():void = Print("{tagged(int, string){Tag := "x"}.Area()}")
