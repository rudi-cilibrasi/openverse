# a deep chain of waiting frames through dispatches that refine type arguments
# (#362): Call, generic over base(t), calls Run, which ib (fixing t to int)
# and gb (adding u, which the dispatch opens, #251) override; ib calls Call on
# a gb, and each gb on another one level down, whose last level sleeps
base(t:type) := class<abstract>:
    X:t
    Run(N:int)<suspends>:t
ib := class(base(int)):
    Run<override>(N:int)<suspends>:int =
        defer:
            Print("ib {N} done")
        Call(gb(int, string){X := X + 1, Y := "y"}, N - 1) + 1
gb(t:type, u:type) := class(base(t)):
    Y:u
    Run<override>(N:int)<suspends>:t =
        defer:
            Print("gb {N} done")
        Sleep(0.01)
        if (N = 0):
            for (I := 1..3):
                Sleep(0.01)
            X
        else:
            Call(gb(t, u){X := X, Y := Y}, N - 1)
Call(B:base(t), N:int where t:type)<suspends>:t = B.Run(N)
Main()<suspends>:void =
    Print("result {Call(ib{X := 1}, 9)}")
    Print("string {Call(gb(string, int){X := "s", Y := 1}, 6)}")
