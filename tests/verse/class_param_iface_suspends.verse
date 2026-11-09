# a <suspends> interface method overridden in a parametric class (#276, via
# #251's opened calls), a race's loser unwound, and a cast from the
# interface that opens the class's type parameter
job := interface:
    Run()<suspends>:int
waitbox(t:type) := class(job):
    Items:[]t
    Run<override>()<suspends>:int =
        defer:
            Print("waitbox unwound")
        Sleep(0.1)
        Items.Length
named := interface:
    Name():string
box(t:type) := class(named):
    V:t
    Name<override>():string = "box"
waitbox2 := class(named):
    Name<override>():string = "w2"
RunAll(Js:[]job)<suspends>:int =
    var T:int = 0
    for (J : Js) { set T += J.Run() }
    T
Main()<suspends>:void =
    Print("{RunAll(array{waitbox(int){Items := array{1, 2}}, waitbox(string){Items := array{"a"}}})}")
    J:job = waitbox(logic){Items := array{true, false, true}}
    W := race:
        J.Run()
        block:
            Sleep(0.05)
            99
    Print("{W}")
    N:named = box(int){V := 5}
    if (B := box[N]) then Print("a box: {B.Name()}") else Print("not a box")
    M:named = waitbox2{}
    if (B := box[M]) then Print("a box") else Print("not a box")
