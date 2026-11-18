# #704 follow-up: a struct in an object's field, replaced by another task
# while the right operand is suspended. OpenVerse: "task 50" (the update goes
# to the replaced struct), then the control "alone 2". Reading the field
# after the right operand: "task 51".
pair := struct<computes>:
    N:int = 0

cell := class:
    var S:pair = pair{N := 1}

Later(C:cell)<suspends>:void =
    Sleep(0.1)
    set C.S = pair{N := 50}

Slow()<suspends>:int =
    Sleep(0.5)
    1

Main()<suspends>:void =
    C := cell{}
    spawn{Later(C)}
    set C.S.N += Slow()
    Print("OVPROBE task {C.S.N}")
    D := cell{}
    set D.S.N += Slow()
    Print("OVPROBE alone {D.S.N}")
