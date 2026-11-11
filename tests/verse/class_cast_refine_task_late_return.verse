# A continuing rush arm returns only from that background arm after the rush.
pair(a:type, b:type) := class {}
dup(t:type) := class(pair(t, t)) {}
Run(P:pair(a, b) where a:type, b:type)<suspends>:int =
    defer: Print("late source defer")
    if (D := dup[P]):
        rush:
            block:
                Sleep(0.25)
                Print("late arm return")
                return 99
            block:
                Sleep(0.0)
                1
        Print("late cast ended")
    Sleep(0.5)
    Print("late source continues")
    7
Main()<suspends>:void = Print("late result {Run(dup(int){})}")
