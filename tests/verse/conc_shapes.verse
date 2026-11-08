# race arms of different types (joined as an if's branches), a first arm
# that declares, an expected tuple type for sync, and 40 races in a row
# (code size grows linearly) (#156, review of #158)
W()<suspends>:int =
    Sleep(1.0)
    1
Work()<suspends>:int =
    Sleep(5.0)
    1
Main()<suspends>:void =
    race:
        Work()
        Sleep(1.0)
    Print("timed out")
    sync:
        X := W()
        W()
    T:tuple([]int, int) = sync:
        block:
            Sleep(1.0)
            array{}
        W()
    Print("{T(0).Length} {T(1)}")
    var N:int = 0
    for (I := 1..40):
        R := race:
            block:
                Sleep(1.0 / 30.0)
                N + 1
            block:
                Sleep(2.0 / 30.0)
                0
        set N = R
    Print("{N}")
