# regression test from the #53 re-review (q38)
holder(t:type) := interface:
    A:t
fix := class(holder(string)):
    M:int = 0
Main():void = Print("x")
