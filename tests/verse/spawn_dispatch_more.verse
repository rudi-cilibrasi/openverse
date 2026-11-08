# spawning dispatched methods: through an interface, from an immediate
# function, of a generic class at a closed type, in a generic function
runner := interface:
    Go(X:int)<suspends>:string
walker := class(runner):
    Go<override>(X:int)<suspends>:string = "walker {X}"
sprinter := class(runner):
    Go<override>(X:int)<suspends>:string =
        Sleep(2.0)
        "sprinter {X}"
box(t:type) := class:
    V:t
    Get()<suspends>:t = V
int_box := class(box(int)):
    Get<override>()<suspends>:int =
        Sleep(1.0)
        V + 100
Kick(R:runner):task(string) = spawn{R.Go(7)}
Count(B:box(t), R:runner where t:type)<suspends>:int =
    T := spawn{R.Go(1)}
    T.Await().Length
Main()<suspends>:void =
    B:box(int) = int_box{V := 5}
    T1 := spawn{B.Get()}
    T2 := Kick(sprinter{})
    T3 := Kick(walker{})
    Print("{T3.Await()}")
    Print("{T1.Await()}")
    Print("{T2.Await()}")
    Print("{Count(int_box{V := 2}, sprinter{})}")
    B2:box(string) = box(string){V := "s"}
    Print("{spawn{B2.Get()}.Await()}")
