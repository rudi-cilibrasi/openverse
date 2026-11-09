# the names a generator's clauses bind, saved with its items: an alternative after its call of itself sees them as they were (#246)
thing := class:
    Name:string = ""
Names(Ts:[]thing, I:int)<computes><decides>:string =
    I < Ts.Length
    T := Ts[I]
    N := T.Name
    N | Names[Ts, I + 1] | "after {N}"
Main():void =
    Ts := array{thing{Name := "a"}, thing{Name := "b"}}
    for (S := Names[Ts, 0]) { Print(S) }
    if (S := Names[Ts, 0], S = "after b") then Print("found {S}")
