# GetRandomInt (#724; the Book's Runtime API reference, /Verse.org/Random;
# UEFN 43.12 admits and runs it, followup-refused/get-random-int). openverse
# is deterministic (LANGUAGE.md, "Random numbers, the clock and the player
# map"): it draws from a generator with a fixed seed, in [Low, High] with
# the bounds in either order, each argument evaluated once; a failure
# context that fails undoes its draws.
using { /Verse.org/Random }
Roll()<transacts>:int = GetRandomInt(1, 6)
Arg(Label:string, N:int):int =
    Print(Label)
    N
Main():void =
    Print("{GetRandomInt(3, 3)}")
    Print("{GetRandomInt(1, 6)} {GetRandomInt(1, 6)} {GetRandomInt(6, 1)} {Roll()}")
    Print("{GetRandomInt(-10, 10)}")
    # a range past 64 bits: 10^24 (printed in two halves; an int past 64
    # bits has no ToString)
    Big := GetRandomInt(0, 1000000000000 * 1000000000000)
    if (Hi := Quotient[Big, 1000000000000], Lo := Mod[Big, 1000000000000]) then Print("{Hi} {Lo}")
    # each argument once, in order
    Print("{GetRandomInt(Arg("low", 1), Arg("high", 2))}")
    var Sum:int = 0
    var Low:int = 0
    var High:int = 0
    for (I := 1..1000):
        R := GetRandomInt(-2, 2)
        if (R < -2 or R > 2) then Print("out of range")
        if (R = -2) then set Low += 1
        if (R = 2) then set High += 1
        set Sum += R
    Print("sum {Sum} lows {Low} highs {High}")
    # a failure context that fails undoes its draws: B is the draw A was
    if (A := GetRandomInt(1, 100), A > 1000) {}
    B := GetRandomInt(1, 100)
    Print("{B}")
