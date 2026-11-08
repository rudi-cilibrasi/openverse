# methods as values (#210): an override reached through a value of the base
# class; <decides> and <suspends> methods as values; the receiver is
# evaluated once, when the value is made
animal := class:
    Name():string = "animal"
dog := class(animal):
    Name<override>():string = "dog"
picky := class:
    Min:int
    Keep(X:int)<decides>:int =
        X >= Min
        X
sleeper := class:
    D:float
    Nap(X:int)<suspends>:int =
        Sleep(D)
        X + 1
tally := class:
    var Made:int = 0
    Make():picky =
        set Made += 1
        picky{Min := 3}
Show(F:type{_():string}):string = F()
Filter(Xs:[]int, F:type{_(:int)<decides>:int}):[]int = for (X : Xs, Y := F[X]) { Y }
RunNap(F:type{_(:int)<suspends>:int})<suspends>:int = F(1)
Main()<suspends>:void =
    A:animal = dog{}
    Print(Show(A.Name))
    T := tally{}
    K := T.Make().Keep
    Print("{Filter(array{1, 5, 2, 4}, K).Length} {Filter(array{3}, K).Length} made {T.Made}")
    S := sleeper{D := 0.1}
    Print("{RunNap(S.Nap)}")
    race:
        RunNap(sleeper{D := 0.5}.Nap)
        RunNap(S.Nap)
    Print("raced")
