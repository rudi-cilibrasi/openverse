# sync: the tuple of its arms' results, whatever order they finish in, and
# the order in which the arms start.
# Tests LANGUAGE.md, Concurrency (Book ch. 14): sync runs its arms
# concurrently and gives the tuple of their results when all have finished.
# Each arm prints as it starts; the sleeps are 0.2 s apart; the third arm
# returns without suspending.
# OpenVerse prints (Lean and C agree):
#   start slow | start fast | start plain | end fast | end slow
#   result 10 2 3
Slow(N:int)<suspends>:int =
    Print("OVPROBE start slow")
    Sleep(0.4)
    Print("OVPROBE end slow")
    N * 10

Fast(N:int)<suspends>:int =
    Print("OVPROBE start fast")
    Sleep(0.2)
    Print("OVPROBE end fast")
    N

Plain(N:int)<suspends>:int =
    Print("OVPROBE start plain")
    N

Main()<suspends>:void =
    R := sync:
        Slow(1)
        Fast(2)
        Plain(3)
    Print("OVPROBE result {R(0)} {R(1)} {R(2)}")
