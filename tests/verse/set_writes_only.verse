# a plain = path needs only <writes> (#58 review)
cc := class:
    var C:int = 0
vs := struct:
    H:cc
W(V:vs)<writes>:void =
    set V.H.C = 5
Main():void =
    V := vs{H := cc{}}
    W(V)
    Print("{V.H.C}")
