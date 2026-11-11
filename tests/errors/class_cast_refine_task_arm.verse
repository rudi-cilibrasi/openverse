# expect: or an arm of sync, race, rush or branch
pair(a:type, b:type) := class {}
dup(t:type) := class(pair(t, t)) {}
Run(P:pair(a, b) where a:type, b:type)<suspends>:void =
    sync:
        block:
            if (D := dup[P]):
                branch: Sleep(1.0)
            Sleep(0.0)
        Sleep(0.0)
Main()<suspends>:void = Run(dup(int){})
