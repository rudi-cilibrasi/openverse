Big():string =
    var S:string = "a"
    var K:int = 0
    loop:
        if (K = 23) { break }
        set S = S + S
        set K += 1
    S + S.Slice[0, 4194304] or S
Down(N:int, S:string):int =
    if (N = 0):
        Print(S)
        0
    else:
        1 + Down(N - 1, S)
Main():void =
    S := Big()
    Print("{Down(4000, S)}")
