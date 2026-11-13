# expect: 6:6: a choice (a | b) has several values, so it must be in a failure context that takes them: an if condition, a for's clauses, first{…}, option{…}, logic{…}, not, or the left of or (#208); a <suspends> function cannot have several values, as a call of it would be in a failure context, which cannot suspend (#156)
# (#283) A <suspends> function has one value: a call of one with several would be in a failure
# context, which cannot suspend.
W(N:int)<suspends>:int =
    Sleep(0.0)
    N | N + 1
Main()<suspends>:void =
    for (X := W(1)) { Print("{X}") }
