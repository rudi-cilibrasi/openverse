# expect: rush cannot be in a loop or for body
pair(a:type, b:type) := class {}
dup(t:type) := class(pair(t, t)) {}
Run(P:pair(a, b) where a:type, b:type)<suspends>:void =
    loop:
        if (D := dup[P]):
            rush:
                Sleep(1.0)
                Sleep(0.0)
        break
Main()<suspends>:void = Run(dup(int){})
