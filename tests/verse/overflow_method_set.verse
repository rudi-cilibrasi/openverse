# A method's `set C += 1` is checked addition: at the largest int it stops
# the program with the overflow error there, before the method returns, so
# before its caller goes on (`t2` is not printed); fuzz-model-mv seed 4594,
# whose model had it after
ctr := class:
    var C:int = 0
    Next()<transacts>:int =
        set C += 1
        C - 1
    Add(X:int)<transacts>:int =
        set C += X
        C
Tell(S:string, X:int):int =
    Print(S)
    X
Main():void =
    K := ctr{C := 4611686018427387903}
    Print("{K.Add(Tell("t1", K.Next()))}")
    Print("{K.Add(Tell("t2", K.Next()))}")
