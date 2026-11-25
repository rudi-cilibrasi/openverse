# ToString of an int beyond 64 bits is the overflow error (#724), and an
# interpolated value is made text where it is written: the program stops
# there, before the arguments of the call with several values in the next
# value run (#723: "c" was printed first, the call's clauses being lifted
# before the string was made).
Tell(S:string, X:int)<transacts>:int =
    Print(S)
    X
Big(X:int)<transacts>:int = 9223372036854775807 + X
Two(X:int)<transacts>:int = X | X + 1
Main():void =
    Print("start")
    if (T := "<{Big(1)}-{Two(Tell("c", 1))}>", T.Length > 1) then Print(T) else Print("no")
    Print("not reached")
