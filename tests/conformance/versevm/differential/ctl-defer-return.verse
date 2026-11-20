# defer with return: a return from inside nested blocks and a loop runs the
# defers of every scope it leaves, innermost first, after the return's value.
# Tests LANGUAGE.md, defer: "at the scope's end, after its value is
# computed, or on a return or break that leaves it"; Lowering: "before each
# return (after its value)".
# OpenVerse prints (Lean and C agree):
#   iteration defer 1 | compute found | iteration defer 2 | function defer
#   got 20 | iteration defer 1 | iteration defer 2 | iteration defer 3
#   iteration defer 4 | iteration defer 5 | compute fallthrough
#   function defer | got -1
Value(S:string, V:int):int =
    Print("OVPROBE compute {S}")
    V

Locate(Target:int):int =
    defer:
        Print("OVPROBE function defer")
    for (X := 1..5):
        defer:
            Print("OVPROBE iteration defer {X}")
        if (X = Target):
            return Value("found", X * 10)
    Value("fallthrough", -1)

Main():void =
    Print("OVPROBE got {Locate(2)}")
    Print("OVPROBE got {Locate(9)}")
