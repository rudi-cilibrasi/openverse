# block: clauses of a class (Book of Verse ch. 10): they run when an
# instance is constructed, after its fields are given, those of the classes
# above it first, and see its fields by name. Their effects are those of
# their code (a block that only prints lets <computes> code construct).

counter := class:
    Name:string
    var Count:int = 0
    block:
        set Count = Name.Length
    block:
        Print("made {Name}")

doubled := class(counter):
    block:
        set Count *= 2
        Print("doubled {Name} to {Count}")

quiet := class<computes>:
    N:int
    block:
        Print("quiet {N}")

Make(N:int)<computes>:quiet = quiet{N := N}

Main():void =
    C := counter{Name := "abc"}
    Print("{C.Count}")
    D := doubled{Name := "hello"}
    Print("{D.Count}")
    Q := Make(7)
    Print("{Q.N}")
