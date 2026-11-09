# opened <suspends> overrides (#251): nested ones, one that hides a type
# argument, a call in a loop (a frame per call, its value unused), a race's
# loser and a cancelled task unwinding one, with its defer
job(t:type) := class<abstract>:
    Run()<suspends>:t
lit := class(job(int)):
    V:int
    Run<override>()<suspends>:int =
        Sleep(0.1)
        V
str := class(job(string)):
    S:string
    Run<override>()<suspends>:string =
        Sleep(0.2)
        S
# hides b: a dispatch from job(a) opens it
fstJ(a:type, b:type) := class(job(a)):
    L:job(a)
    R:job(b)
    Run<override>()<suspends>:a =
        defer:
            Print("fst unwound")
        X := L.Run()
        R.Run()
        X
pairJ(a:type, b:type) := class(job(tuple(a, b))):
    L:job(a)
    R:job(b)
    Run<override>()<suspends>:tuple(a, b) =
        X := L.Run()
        Y := R.Run()
        (X, Y)
Go(J:job(t) where t:type)<suspends>:t = J.Run()
Many(J:job(t), N:int where t:type)<suspends>:int =
    var C:int = 0
    for (I := 1..N):
        J.Run()
        set C += 1
    C
Fast(J:job(t), X:t where t:type)<suspends>:t =
    race:
        J.Run()
        block:
            Sleep(0.15)
            X
Main()<suspends>:void =
    P := Go(pairJ(int, string){L := lit{V := 1}, R := str{S := "s"}})
    Print("{P(0)} {P(1)}")
    Q := Go(pairJ(tuple(int, string), int){L := pairJ(int, string){L := lit{V := 3}, R := str{S := "t"}}, R := lit{V := 4}})
    Print("{Q(0)(0)} {Q(0)(1)} {Q(1)}")
    Print("{Go(fstJ(int, string){L := lit{V := 5}, R := str{S := "u"}})}")
    Print("many {Many(fstJ(int, string){L := lit{V := 6}, R := str{S := "v"}}, 3)}")
    Print("fast {Fast(fstJ(int, string){L := lit{V := 7}, R := str{S := "w"}}, 99)}")
    T := spawn{Go(fstJ(int, string){L := lit{V := 8}, R := str{S := "x"}})}
    Sleep(0.15)
    T.Cancel()
    Print("cancelled")
