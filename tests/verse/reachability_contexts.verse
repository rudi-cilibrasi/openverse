# Code never reached in and after failure contexts (Book of Verse ch. 7; its
# tests, FlowControl/Reachability.versetest). No return or break leaves an
# if's conditions, a for's clauses, option{…}, not's operand or the left of
# or (Reachability.versetest:12, SOL-4199-BreakFromIf.versetest), so each
# completes or fails, and the code after it is reached; a loop of their own
# takes a break in them, and the code after that break is never reached.
# The left of `and` is no failure context: a break there leaves the `and`
# before its right.
Main():void =
    var N:int = 0
    if (block{loop{break; set N += 1}; N = 0}) then Print("if {N}")
    for (X := 1..3, block{loop{break; set N += 10}; X > 2}) do Print("for {X} {N}")
    O:?int = option{loop{break; set N += 100}; N}
    if (not (loop{break; set N += 1000}; N > 0)) then Print("not {N}")
    Y:int = (loop{break; set N += 10000}; O?) or 7
    Print("or {Y} {N}")
    loop:
        (break) and (set N += 100000)
    Print("and {N}")
