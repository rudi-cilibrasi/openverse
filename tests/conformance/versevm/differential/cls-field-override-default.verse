# A subclass overriding a field's default, an archetype overriding both, and
# the parent's method reading the field.
# Tests LANGUAGE.md, Classes (ch. 10): a field's default overridden in a
# subclass (<override> on a field), read by the parent's method through the
# instance.
# OpenVerse prints (Lean and C agree):
#   4 ... / 2 tweet / 1 tweet
animal_cls := class:
    Legs:int = 4
    Sound:string = "..."
    Describe()<computes>:string = "{Legs} {Sound}"

bird_cls := class(animal_cls):
    Legs<override>:int = 2
    Sound<override>:string = "tweet"

Main():void =
    A := animal_cls{}
    B := bird_cls{}
    C := bird_cls{Legs := 1}
    Print("OVPROBE {A.Describe()} / {B.Describe()} / {C.Describe()}")
