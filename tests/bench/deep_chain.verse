# a recursion of depth 400 whose every level waits on its child, which sleeps
# 400 ticks: the scheduler resumes the waiting leaf directly (#362; DESIGN.md,
# "Resuming the waiting frame directly"), so the cost is linear in the depth
# (before, each pass resumed the whole chain from its root: about 400 × 400
# resumptions)
Deep(N:int)<suspends>:int =
    if (N = 0):
        for (I := 1..400):
            Sleep(0.1)
        0
    else:
        Deep(N - 1) + 1
Main()<suspends>:void =
    Print("{Deep(400)}")
