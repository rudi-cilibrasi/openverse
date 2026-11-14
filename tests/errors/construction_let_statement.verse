# expect: a let: clause of a construction has only definitions, X := e
# (Book of Verse ch. 10: "Unlike block, let permits only declarations")
point := struct:
    X:int
Main():void =
    var Y:int = 0
    P := point:
        let:
            set Y = 1
        X := Y
