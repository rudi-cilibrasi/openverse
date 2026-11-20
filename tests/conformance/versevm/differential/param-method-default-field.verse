# A method's named parameter whose default reads a field of the object, a
# var field changed between calls.
# Tests LANGUAGE.md, Functions: "a default may use the parameters before
# it, and a method's default the method's fields"; "a default is evaluated
# at the call".
# OpenVerse prints (Lean and C agree):
#   30 70 10
gauge := class:
    var Level:int = 3
    Show(?At:int = Level)<reads>:int = At * 10

Main():void =
    G := gauge{}
    A := G.Show()
    set G.Level = 7
    B := G.Show()
    C := G.Show(?At := 1)
    Print("OVPROBE {A} {B} {C}")
