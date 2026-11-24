# A defer of a function that cannot suspend may spawn (#724): the Book's
# tests, FlowControl/defer.versetest:1094 ("Ensure that defer allows
# immediate `spawn` expression"), and Epic's compiler and Verse VM (UEFN
# 43.12, followup-refused/spawn-in-defer). The task starts where the defer
# runs, at each exit of its scope, and runs to its first wait before the
# defer goes on. In a <suspends> function it is refused
# (errors/class_cast_context_defer_spawn).
Coro()<suspends>:void = {}
Slow(N:int)<suspends>:void =
    Print("slow {N} starts")
    Sleep(0.1)
    Print("slow {N} ends")
Quick(N:int)<suspends>:int =
    Print("quick {N}")
    N * 2
F():void =
    defer:
        spawn{Slow(1)}
        Print("after spawn in F's defer")
    Print("F body")
Early(N:int):int =
    defer:
        T := spawn{Quick(N)}
        Print("after spawn in Early's defer")
    if (N > 1) then return 1
    Print("Early goes on")
    0
Looping():void =
    var I:int = 0
    loop:
        defer:
            spawn{Slow(10 + I)}
        set I += 1
        if (I = 2) then break
    Print("looped {I}")
Probe():void =
    defer:
        spawn{Coro()}
        Print("after spawn in defer")
    Print("body")
Main()<suspends>:void =
    Probe()
    F()
    Print("{Early(2)} {Early(1)}")
    Looping()
    Sleep(1.0)
    Print("end")
