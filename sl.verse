Big():string =
    var S:string = "a"
    var K:int = 0
    loop:
        if (K = 16) { break }
        set S = S + S
        set K += 1
    S.Slice[0, 1000] or S
Main():void = Print("{Big().Length}")
