# a recursion of depth 400 whose every level waits on its child, which sleeps
# 400 ticks: each pass of the scheduler resumes the whole chain from its root,
# so the program makes about 400 × 400 resumptions (DESIGN.md, "Each pass
# resumes a whole chain"); a baseline for a scheduler that resumes the waiting
# leaf directly
Deep(N:int)<suspends>:int =
    if (N = 0):
        for (I := 1..400):
            Sleep(0.1)
        0
    else:
        Deep(N - 1) + 1
Main()<suspends>:void =
    Print("{Deep(400)}")
