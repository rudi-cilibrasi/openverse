# a generic method's calls on Self dispatch to the overrides of a class
# that fixes the type argument (#142, #171), with void and t results
box(t:type) := class:
    var V:t
    Get()<suspends>:t = V
    Put(X:t)<suspends>:void = set V = X
    Bump()<suspends>:t =
        Put(Get())
        Get()
int_box := class(box(int)):
    Get<override>()<suspends>:int =
        Sleep(0.0)
        V + 1
    Put<override>(X:int)<suspends>:void =
        Sleep(1.0)
        set V = X * 10
Use(B:box(t), X:t where t:type)<suspends>:t =
    B.Put(X)
    B.Bump()
Main()<suspends>:void =
    Print("{Use(int_box{V := 0}, 2)}")
    Print("{Use(box(string){V := ""}, "q")}")
    # the same call site again: its frame is reset, not made anew
    var I:int = 0
    loop:
        if (I = 3) then break
        Print("{Use(int_box{V := I}, I)}")
        set I += 1
