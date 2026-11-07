# Parametric functions (Book of Verse, Types: where clauses). Each generic
# function is checked once with its type parameters opaque, then elaborated
# once per instantiation.

Identity(X:t where t:type):t = X

Swap(P:tuple(t, u) where t:type, u:type):tuple(u, t) = (P(1), P(0))

Combine(A:t1, B:t2 where t1:type, t2:type):tuple(t1, t2) = (A, B)

# a comparable type parameter supports = and <>
Find(Items:[]t, Target:t where t:subtype(comparable))<decides>:int =
    var Result:int = -1
    for (I -> X : Items, Result < 0, X = Target):
        set Result = I
    Result >= 0
    Result

Contains(Items:[]t, Target:t where t:subtype(comparable))<decides>:void =
    Find[Items, Target]

First(Items:[]t where t:type)<decides>:t = Items[0]

Last(Items:[]t where t:type)<decides>:t = Items[Items.Length - 1]

Reverse(Items:[]t where t:type):[]t =
    var Out:[]t = array{}
    for (X : Items):
        set Out = array{X} + Out
    Out

# recursion within one instance
Repeat(X:t, N:int where t:type):[]t =
    if (N <= 0) then array{} else array{X} + Repeat(X, N - 1)

# generic code calling generic code
Twice(X:t where t:type):tuple(t, t) = Combine(Identity(X), X)

Pairs(Items:[]t where t:type):[]tuple(t, t) =
    for (X : Items) { Twice(X) }

# t appears only in the result: it is inferred from the expected type
Nothing(N:int where t:type):?t = false

Unwrap(O:?t, Default:t where t:type):t =
    if (V := O?) then V else Default

Lookup(M:[k]v, Key:k, Default:v where k:subtype(comparable), v:type):v =
    if (V := M[Key]) then V else Default

Dedup(Items:[]t where t:subtype(comparable)):[]t =
    var Out:[]t = array{}
    for (X : Items):
        if (not Contains[Out, X]):
            set Out += array{X}
    Out

# a helper of any type, used by generic code instantiated at void
Fail(Msg:string where t:type):t =
    Print(Msg)
    Err()

Checked(X:t, Ok:int where t:type):t =
    if (Ok > 0) then X else Fail("not ok")

Log():void = Print("logged")

# instances are the generically checked body: = against a literal means the
# same at every type argument
IsTrue(X:t where t:subtype(comparable))<decides>:void = X = true

# constants may call generic functions, and refer to constants defined later
Answer := Identity(Later)
Later := 42
Names:[]string = Repeat("n", 2)

point := struct:
    X:int = 0
    Y:int = 0

ShowInts(Items:[]int):string =
    var S:string = ""
    for (I -> X : Items):
        if (I > 0) then set S += ", "
        set S += ToString(X)
    "[{S}]"

Main():void =
    Print("{Identity(42)} {Identity("hello")} {Identity('c')}")
    S := Swap((1, "one"))
    Print("{S(0)} {S(1)}")
    C := Combine(point{X := 3}, array{true, false})
    Print("({C(0).X}, {C(0).Y}) {C(1).Length}")
    if (I := Find[array{"apple", "banana", "cherry"}, "banana"]) then Print("banana at {I}")
    if (not Find[array{1, 2, 3}, 7]) then Print("no 7")
    if (Contains[array{point{X := 1}, point{Y := 2}}, point{Y := 2}]) then Print("found a point")
    if (F := First[array{10, 20, 30}], L := Last[array{10, 20, 30}]) then Print("{F} .. {L}")
    if (not First[Reverse(Repeat(1, 0))]) then Print("an empty instance")
    Print(ShowInts(Reverse(array{1, 2, 3, 4})))
    Print(Reverse("stressed"))
    for (P : Pairs(array{5, 6})) { Print("{P(0)}{P(1)}") }
    var Grid:[][]int = Repeat(Repeat(0, 3), 2)
    if (set Grid[1] = array{7, 8, 9}, Row := Grid[1]) then Print("{Grid.Length} rows, last {ShowInts(Row)}")
    E:[]string = Reverse(array{})
    Print("empty: {E.Length}")
    Print("{Unwrap(option{3}, 0)} {Unwrap(false, "default")}")
    O:?string = Nothing(1)
    Print(Unwrap(O, "nothing"))
    M := map{"a" => 1, "b" => 2}
    Print("{Lookup(M, "b", 0)} {Lookup(M, "z", -1)}")
    Print(ShowInts(Dedup(array{3, 1, 3, 2, 1})))
    Print(Dedup("mississippi"))
    Print("{Checked(7, 1)}")
    Checked(Log(), 1)
    if (IsTrue[true]) then Print("true is true")
    if (not IsTrue[1], not IsTrue[option{true}]) then Print("1 and an option are not")
    Print("{Answer} {Names.Length}")
    # an instance that fails rolls back like any <decides> call
    var Count:int = 0
    if (set Count += 1, First[Repeat(0, 0)]) then Print("unreachable")
    Print("Count = {Count}")
