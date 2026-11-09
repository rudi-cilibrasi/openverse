# branches started from loops: one call site of a function with nested (#254, from the review of #258)
# branches and a rush, run 3 times (its frame reused), and 3 spawned tasks of
# it, cancelled in turn
F(N:int, D:float)<suspends>:int =
    defer:
        Print("F{N} defer")
    branch:
        defer:
            Print("F{N} A defer")
        X := rush:
            block:
                defer:
                    Print("F{N} A.r1 defer")
                branch:
                    defer:
                        Print("F{N} A.r1.b defer")
                    Sleep(5.0)
                Sleep(5.0)
                1
            block:
                Sleep(0.1)
                2
        Sleep(0.1)
        branch:
            defer:
                Print("F{N} A.1 defer")
            Sleep(5.0)
        Sleep(5.0)
    branch:
        defer:
            Print("F{N} B defer")
        Sleep(5.0)
    Sleep(D)
    N
Main()<suspends>:void =
    var I:int = 0
    loop:
        if (I = 3) then break
        Print("{F(I, 0.5)}")
        set I += 1
    var Ts:[]task(int) = array{}
    for (J := 0..2):
        set Ts += array{spawn{F(10 + J, 9.0)}}
    Sleep(1.0)
    for (T : Ts):
        T.Cancel()
        Print("cancelled")
    Print("end")
