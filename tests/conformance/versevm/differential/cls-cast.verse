# Dynamic casts of objects to a subclass: success, failure, and a cast to an
# interface.
# Tests LANGUAGE.md, Supported, Classes: "casts T[X] and T(X)".
# OpenVerse prints (Lean and C agree):
#   pet not dog cat label | pet dog 3 unnamed | pet not dog unnamed
named := interface:
    Label()<computes>:string

pet_cls := class:
    Kind:string = "pet"

cat_cls := class(pet_cls, named):
    Label<override>()<computes>:string = "cat label"

dog_cls := class(pet_cls):
    Barks:int = 3

Main():void =
    Pets:[]pet_cls = array{cat_cls{}, dog_cls{}, pet_cls{}}
    for (P : Pets):
        A := if (D := dog_cls[P]) then "dog {D.Barks}" else "not dog"
        B := if (N := named[P]) then N.Label() else "unnamed"
        Print("OVPROBE {P.Kind} {A} {B}")
