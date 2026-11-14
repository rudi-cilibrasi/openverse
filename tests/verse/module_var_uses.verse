# Module-scoped vars used from everywhere a variable can be: two modules'
# vars of one name, a <suspends> function under sync and in a spawned task,
# a refining cast's branches, a choice, a generic function, a for whose
# iterations fail, and a class's methods (docs/research/weak-map.md). The
# key class is not <persistent>, so its values need not persist (the API
# reference's `session`).

player := class<unique><module_scoped_var_weak_map_key>:
    Name:string
animal := class<unique>:
    Legs:int
dog := class(animal):
    Bark:string = "woof"

A := module:
    var Count<public>:weak_map(player, int) = map{}
B := module:
    var Count<public>:weak_map(player, string) = map{}
var Seen:weak_map(player, []int) = map{}

Bump(P:player)<transacts><decides>:void =
    if (C := A.Count[P]):
        set A.Count[P] = C + 1
    else:
        set A.Count[P] = 1

Tick(P:player, N:int)<suspends>:void =
    for (I := 1..N):
        Sleep(0.0)
        if (Bump[P]) {}

Describe(X:animal, P:player)<transacts>:void =
    if (D := dog[X]):
        if (set B.Count[P] = D.Bark) {}
    else:
        if (set B.Count[P] = "{X.Legs} legs") {}

Pick(P:player)<transacts><decides>:int = (A.Count[P] | 100)

Gen(P:player, X:t where t:type)<transacts>:t =
    if (set Seen[P] = array{1}) {}
    X

counter := class:
    P:player
    Add(N:int)<transacts><decides>:void =
        Old := A.Count[P] or 0
        set A.Count[P] = Old + N
    Get()<transacts>:int = A.Count[P] or 0

Main()<suspends>:void =
    P := player{Name := "p"}
    Q := player{Name := "q"}
    sync:
        Tick(P, 3)
        Tick(Q, 2)
    if (C := A.Count[P], D := A.Count[Q]) then Print("counts {C} {D}")
    Describe(dog{Legs := 4}, P)
    Describe(animal{Legs := 6}, Q)
    if (S := B.Count[P], T := B.Count[Q]) then Print("says {S} / {T}")
    if (V := Pick[P]) then Print("pick {V}")
    for (I := 1..5, I <> 3):
        if (set Seen[P] = array{I}, I = 4) {}
    if (S := Seen[P], S0 := S[0]) then Print("seen {S0}")
    Y := Gen(Q, 7)
    if (S := Seen[Q], S0 := S[0]) then Print("gen {Y} {S0}")
    T := spawn{Tick(P, 1)}
    T.Await()
    if (C := A.Count[P]) then Print("after spawn {C}")
    R := player{Name := "r"}
    C1 := counter{P := R}
    if (C1.Add[5], C1.Add[6]) {}
    C2 := counter{P := R}
    Print("counter {C1.Get()} {C2.Get()} {counter{P := player{Name := "s"}}.Get()}")
