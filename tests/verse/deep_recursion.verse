# Recursion that never ends is a resource limit, not a crash (#97): both
# implementations stop at their depth bound with `limit: recursion depth`,
# exit 3, and print nothing (the output is part of the final state).
Spin(N:int):int = Spin(N + 1)

Main():void =
    Print("start")
    Print("{Spin(0)}")
