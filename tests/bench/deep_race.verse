# deep_chain's recursion (depth 400, its leaf sleeping 400 ticks) as an arm
# of a race against a timeout: the arm records the waiting frame its chain
# found, and each pass resumes it directly (#362), linear in the depth (before,
# each pass resumed the arm's whole chain: 1.8 s in the reference interpreter)
Deep(N:int)<suspends>:int =
    if (N = 0):
        for (I := 1..400):
            Sleep(0.01)
        0
    else:
        Deep(N - 1) + 1
Main()<suspends>:void =
    R := race:
        Deep(400)
        block:
            Sleep(1000.0)
            -1
    Print("{R}")
