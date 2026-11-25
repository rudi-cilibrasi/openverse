# Extension methods on int, string and arrays, one of them <decides>.
# Tests LANGUAGE.md, Extension methods: "(R:t).M(...)<effects>:r = body ...
# called X.M(...), or X.M[...] when <decides>".
# OpenVerse prints (Lean and C agree):
#   42 hey! 6 | -1 11
(N:int).Doubled():int = N * 2

(S:string).Shout():string = S + "!"

(A:[]int).Total():int =
    var S:int = 0
    for (X : A):
        set S += X
    S

(N:int).HalfOf()<computes><decides>:int =
    Mod[N, 2] = 0
    Quotient[N, 2]

Main():void =
    K:int = 21
    Print("OVPROBE {K.Doubled()} {"hey".Shout()} {array{1, 2, 3}.Total()}")
    A := K.HalfOf[] or -1
    B := (K + 1).HalfOf[] or -1
    Print("OVPROBE {A} {B}")
