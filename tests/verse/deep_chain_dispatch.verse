# a deep chain of waiting frames through method dispatch (#362): each level
# calls the next node's <suspends> Run, through its interface (whose frames the
# caller resumes, so the caller records itself) and through a generic class's
# override; the last node sleeps, then every level adds its value
node := interface:
    Run(N:int)<suspends>:int
leaf := class(node):
    K:int
    Run<override>(N:int)<suspends>:int =
        for (I := 1..K):
            Sleep(0.01)
        N
step := class(node):
    V:int
    Next:node
    Run<override>(N:int)<suspends>:int =
        defer:
            Print("step {V} done")
        Next.Run(N + V) + 1
gstep(t:type) := class(node):
    X:t
    Next:node
    Run<override>(N:int)<suspends>:int =
        Sleep(0.01)
        Next.Run(N) + 100
Build(D:int, Tail:node):node =
    if (D = 0) then Tail else Build(D - 1, step{V := D, Next := Tail})
Main()<suspends>:void =
    L := leaf{K := 5}
    G := gstep(string){X := "g", Next := Build(4, L)}
    C := Build(6, G)
    Print("total {C.Run(0)}")
