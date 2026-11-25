# rush: the first arm's value, and the other arm going on after the rush
# returns.
# Tests LANGUAGE.md, Concurrency (Book ch. 14): rush gives the first arm to
# finish and lets the others go on. The sleeps are 0.3 s apart.
# OpenVerse prints (Lean and C agree):
#   finished fast | result 2 | finished slow | after wait
Arm(Name:string, D:float, V:int)<suspends>:int =
    Sleep(D)
    Print("OVPROBE finished {Name}")
    V

Main()<suspends>:void =
    R := rush:
        Arm("slow", 0.6, 1)
        Arm("fast", 0.3, 2)
    Print("OVPROBE result {R}")
    Sleep(0.6)
    Print("OVPROBE after wait")
