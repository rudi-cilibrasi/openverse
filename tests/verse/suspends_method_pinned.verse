# suspends methods dispatched to classes that fix type arguments (#142, #171)
source(t:type) := class:
    Seed:t
    Next(Step:t)<suspends>:t = Seed
ints := class(source(int)):
    Next<override>(Step:int)<suspends>:int =
        defer:
            Print("ints done")
        Sleep(1.0)
        Seed + Step
names := class(source(string)):
    Next<override>(Step:string)<suspends>:string =
        Sleep(2.0)
        "{Seed}-{Step}"
slow := class(source(int)):
    Next<override>(Step:int)<suspends>:int =
        defer:
            Print("slow cancelled or done")
        Sleep(10.0)
        Step
Twice(S:source(t), X:t where t:type)<suspends>:t =
    A := S.Next(X)
    S.Next(A)
Pick(S:source(t), X:t, Fallback:t where t:type)<suspends>:t =
    race:
        S.Next(X)
        block:
            Sleep(3.0)
            Fallback
Main()<suspends>:void =
    Print("{Twice(ints{Seed := 10}, 1)}")
    Print("{Twice(names{Seed := "a"}, "b")}")
    Print("{Twice(source(float){Seed := 1.5}, 2.0)}")
    Print("{Pick(ints{Seed := 1}, 2, 0)}")
    Print("{Pick(slow{Seed := 1}, 2, 99)}")
    var Total:int = 0
    for (I := 1..3):
        set Total += Twice(ints{Seed := I}, I)
    Print("{Total}")
    R := sync:
        Twice(ints{Seed := 100}, 1)
        Twice(names{Seed := "x"}, "y")
    Print("{R(0)} {R(1)}")
