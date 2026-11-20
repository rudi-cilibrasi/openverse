# race: the value of the arm that finishes first, the loser's defer, and
# where the code after the race goes on.
# Tests LANGUAGE.md, Concurrency (Book ch. 14): race gives the first arm to
# finish and cancels the others (their defers run). The sleeps are 0.3 s
# apart.
# OpenVerse prints (Lean and C agree):
#   finished fast | defer fast | defer slow | result 2
Arm(Name:string, D:float, V:int)<suspends>:int =
    defer:
        Print("OVPROBE defer {Name}")
    Sleep(D)
    Print("OVPROBE finished {Name}")
    V

Main()<suspends>:void =
    R := race:
        Arm("slow", 0.6, 1)
        Arm("fast", 0.3, 2)
    Print("OVPROBE result {R}")
