# Control of unique-interface-equality: a class implements the interface, and
# two of its objects are compared. Not a Book case.
# OpenVerse (ce8632ea, Lean and C agreeing) prints
#   compared
# If UEFN 43.12 refuses this too, unique-interface-equality's refusal is not
# the form's.
shape := interface<unique>:
    Sides():int

square := class(shape):
    Sides<override>():int = 4

Same(A:shape, B:shape):logic = if (A = B) then true else false

Main():void =
    S:shape = square{}
    T:shape = square{}
    R1 := Same(S, S)
    R2 := Same(S, T)
    if (R1?, not R2?):
        Print("OVPROBE compared")
