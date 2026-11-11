# Review of #342: a body failure (in a <decides> function, option{} or
# an if condition) must fail the whole for, not one continuation call.
# Outcome continuations must retain this behavior. Also key them with the names their
# alternatives use, as a for copied per alternative has one place but
# alternatives of other types
Two(X:int)<transacts>:int = X | X + 1
Dup(X:t where t:type)<transacts>:t = X | X
G()<transacts><decides>:[]int =
    for (X := (Two(1) | Two(10)), Y := (Two(2) | Two(20))):
        Print("body {X} {Y}")
        X + Y > 12
        X + Y
Main()<transacts>:void =
    if (R := G[]) { Print("G {R.Length}") } else { Print("G failed") }
    O := option{ for (X := (Two(1) | Two(10)), Y := (Two(2) | Two(20))) { X > 5; X } }
    if (W := O?) { Print("opt {W.Length}") } else { Print("opt failed") }
    if (R := for (X := (Two(1) | Two(10)), Y := (Two(2) | Two(20))) { X > 5; X }):
        Print("if {R.Length}")
    else:
        Print("if failed")
    var N : int = 0
    for (A := (Dup(1) | Dup("s"))):
        for (X := (Dup(A) | Dup(A)), Y := (Dup(1) | Dup(2))):
            set N += Y
    Print("n {N}")
