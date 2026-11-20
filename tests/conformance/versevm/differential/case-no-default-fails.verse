# A case without _ in a failure context: a value no arm names makes it fail.
# Tests LANGUAGE.md, Supported, Enums: "a case on one needs _ or a failure
# context"; Control: case with literal patterns. Epic's compiler may require
# _ for ints whatever the context.
# OpenVerse prints (Lean and C agree):
#   one none
Pick(X:int)<computes><decides>:string =
    case (X):
        1 => "one"
        2 => "two"

Main():void =
    A := Pick[1] or "none"
    B := Pick[3] or "none"
    Print("OVPROBE {A} {B}")
