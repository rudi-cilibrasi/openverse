Alt(A:int,B:int):int = A - B | B * 3
Alt(S:string):int = S.Length | 0
Pick(A:int)<computes>:int = A * 5
Pick(S:string)<computes>:int = S.Length | 9
Pick(A:int,B:int)<computes>:int = Pick(A) | Pick("{B}")
Walk(N:int):int =
    Print("visit {N}")
    if (N <= 1) then N else Walk(N - 1) | N
Run(Target:int):void =
    var Count:int = 0
    if (A := 1 | ((0 | 0) + 1), X := Walk(2), set Count += 1,
        Y := Pick((4 | 1) | Alt(0,-1),0), Y = Target):
        Print("first {A} {X} {Y} count {Count}")
    else:
        Print("none {Target} count {Count}")
    Print("after {Count}")
Main():void =
    Run(9)
    Run(5)
    Run(-15)
    Run(40)
