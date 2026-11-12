# A for over three composed choices with filters after them, whose body
# spawns: in the continuation (#335), each alternative's own for (#283)
# keeps the body out of a failure context, as the source has it, so the
# spawn is allowed (it was refused as one in a failure context)
Two(N:int):int = N | N + 1
Shouter(N:int)<suspends>:void =
    Sleep(0.0)
    Print("shout {N}")
Kick():[]int =
    for (A0 := (Two(0) | Two(2)), A1 := (Two(0) | Two(2)), A2 := (Two(0) | Two(2)), A0 = 0, A1 = 0):
        spawn{Shouter(A2)}
        A2
Main()<suspends>:void =
    R := Kick()
    Print("values {R.Length}")
    Sleep(0.1)
    Print("done")
