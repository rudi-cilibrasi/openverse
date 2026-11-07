# Parametric structs (Book of Verse ch. 9: `wrapper(t:type) := struct`). A
# parametric struct is a family of tuple types in Verse Core: its fields are
# those of the definition with the type arguments substituted.

pair(t:type, u:type) := struct:
    First:t
    Second:u

box(t:type) := struct:
    Items:[]t = array{}
    var Count:int = 0

# a struct whose type argument must be comparable
keyed(k:subtype(comparable), v:type) := struct:
    Entries:[k]v = map{}

point := struct:
    X:int = 0
    Y:int = 0

# a non-parametric struct holding instances
labelled := struct:
    Name:string
    At:pair(int, int)

MakePair(A:t, B:u where t:type, u:type):pair(t, u) = pair(t, u){First := A, Second := B}

Swap(P:pair(t, u) where t:type, u:type):pair(u, t) = pair(u, t){First := P.Second, Second := P.First}

Push(B:box(t), X:t where t:type):box(t) =
    var Out:box(t) = B
    set Out = box(t){Items := Out.Items + array{X}, Count := Out.Count + 1}
    Out

Put(K:keyed(k, v), Key:k, Value:v where k:subtype(comparable), v:type):keyed(k, v) =
    var M:[k]v = K.Entries
    set M[Key] = Value
    keyed(k, v){Entries := M}

Firsts(Ps:[]pair(t, u) where t:type, u:type):[]t = for (P : Ps) { P.First }

Main():void =
    P := pair(int, string){First := 1, Second := "one"}
    Print("{P.First} {P.Second}")
    Q := Swap(P)
    Print("{Q.First} {Q.Second}")
    # type arguments from the expected type
    R:pair(string, int) = pair{First := "two", Second := 2}
    if (Q = R) then Print("unreachable") else Print("different values")
    if (Q = pair(string, int){First := "one", Second := 1}) then Print("equal by value")
    # nesting
    N := MakePair(MakePair(1, 'x'), array{point{X := 3}})
    Print("{N.First.First} {N.First.Second} {N.Second.Length}")
    # defaults are elaborated at the field's type
    var B:box(string) = box(string){}
    set B = Push(Push(B, "a"), "b")
    set B.Count += 10
    Print("{B.Items.Length} items, count {B.Count}")
    E := box(int){}
    Print("empty: {E.Items.Length}")
    var K:keyed(string, int) = keyed(string, int){}
    set K = Put(Put(K, "x", 1), "y", 2)
    set K = Put(K, "x", 3)
    for (Key -> V : K.Entries) { Print("{Key} => {V}") }
    L := labelled{Name := "origin", At := pair(int, int){First := 0, Second := 0}}
    Print("{L.Name} at ({L.At.First}, {L.At.Second})")
    Ps := array{MakePair(1, "a"), MakePair(2, "b"), MakePair(3, "c")}
    for (F : Firsts(Ps)) { Print("{F}") }
    var Cache:[pair(int, int)]string = map{}
    set Cache[MakePair(1, 2)] = "one-two"
    if (V := Cache[pair(int, int){First := 1, Second := 2}]) then Print(V)
