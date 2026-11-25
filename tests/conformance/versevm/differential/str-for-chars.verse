# Iterating a string's chars with for, building a reversed string and a
# filtered one, and the indices of a string.
# Tests LANGUAGE.md, Control: "for with X : array, I -> X : array"; a
# string is a []char, so a for over it gives its chars in order.
# OpenVerse prints (Lean and C agree):
#   desserts 2 0,4,5,
Main():void =
    S:string = "stressed"
    var R:string = ""
    for (C : S):
        set R = array{C} + R
    Vowels := for (C : S, C = 'e') { C }
    var Spots:string = ""
    for (I -> C : S, C = 's'):
        set Spots = Spots + "{I},"
    Print("OVPROBE {R} {Vowels.Length} {Spots}")
