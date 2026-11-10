# <suspends> methods through views (#351): a dispatch to a class whose
# type arguments it opens keeps the callee's frame at them, from a generic
# caller too, and in spawned tasks
container(t:type) := interface:
    Get():t
sink(u:type) := interface:
    Put(X:u)<suspends>:int
both(t:type, u:type) := class(container(t), sink(u)):
    V:t
    var N:int = 0
    Get<override>():t = V
    Put<override>(X:u)<suspends>:int =
        Sleep(0.01)
        set N += 1
        N
one(u:type) := class(sink(u)):
    Put<override>(X:u)<suspends>:int =
        Sleep(0.01)
        100
GP(S:sink(x), V:x where x:type)<suspends>:int = S.Put(V)
Main()<suspends>:void =
    B := both(int, string){V := 3}
    S:sink(string) = B
    Print("{S.Put("a")}")
    T := spawn{S.Put("d")}
    Print("{T.Await()}")
    T2 := spawn{GP(B, "e")}
    Print("{T2.Await()}")
    Print("{GP(one(float){}, 1.0)}")
    Ss:[]sink(string) = array{B, one(string){}}
    for (X : Ss) { Print("{X.Put("c")}") }
