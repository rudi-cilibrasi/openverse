# expect: unknown function
# Without a body on its line, first(…) is a call, of a function no program
# can define (first is reserved): the block on the next line is a statement.
Main():void =
    Y := first(1)
    { Print("block {Y}") }
