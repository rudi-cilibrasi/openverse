# race, rush and sync arms that return while another arm's deep chain waits
# (#362): the waiting frames the chain recorded are cancelled, and forgotten
# when the function ends, so no pass resumes them (each unwinds once)
Deep(N:int, Tag:string)<suspends>:int =
    defer:
        Print("{Tag} {N} unwinds")
    if (N = 0):
        Sleep(0.2)
        Print("{Tag} leaf woke")
        0
    else:
        Deep(N - 1, Tag) + 1
FR()<suspends>:int =
    race:
        block:
            Deep(5, "race")
        block:
            Sleep(0.0)
            return 7
    0
FU()<suspends>:int =
    rush:
        block:
            Deep(5, "rush")
        block:
            Sleep(0.0)
            return 8
    0
# returns on the first run: no pass from a recorded frame needed
FS(Z:int)<suspends>:int =
    sync:
        block:
            Deep(5, "sync0")
        block:
            if (Z > 0):
                Sleep(0.0)
            return 9
    0
P(Which:int)<suspends>:void =
    X := if (Which = 0) then FR() else if (Which = 1) then FU() else FS(0)
    Print("F gave {X}")
    Sleep(0.0)
    Print("P after sleep 1")
    Sleep(0.0)
    Print("P done")
Main()<suspends>:void =
    P(0)
    P(1)
    P(2)
    Sleep(0.5)
    Print("main done")
