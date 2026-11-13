# a recursion of depth 50 waiting at every level (#362): the scheduler resumes
# the waiting leaf directly and, once it ends, the chain from its root; the
# leaf sleeps 30 ticks, each level adds after its child returns
Deep(N:int)<suspends>:int =
    if (N = 0):
        for (I := 1..30):
            Sleep(0.01)
        0
    else:
        Deep(N - 1) + 1
Main()<suspends>:void =
    Print("{Deep(50)}")
