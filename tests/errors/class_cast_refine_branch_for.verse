# expect: branch cannot be in a loop or for body
pair(a:type, b:type) := class {}
dup(t:type) := class(pair(t, t)) {}
Run(P:pair(a, b) where a:type, b:type)<suspends>:void =
    for (N := 1..2):
        if (D := dup[P]):
            if (E := dup[P]):
                branch: Sleep(1.0)
Main()<suspends>:void = Run(dup(int){})
