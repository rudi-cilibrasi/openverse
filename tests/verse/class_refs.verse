# Classes as references (#34, phase 3 of #11; Book of Verse ch. 10): var
# fields seen through aliases, writes undone by failure contexts, objects
# that outlive the function that made them, <unique> identity, and
# recursive classes.

counter := class:
    Name:string
    var Count:int = 0
    # a method writes a field by its bare name
    Bump():int =
        set Count += 1
        Count

holder := struct:
    C:counter

token := class<unique>:
    Label:string

node := class:
    Value:int
    var Next:?node = false

tree := class:
    Key:int
    Left:?tree = false
    Right:?tree = false

MakeBumped(N:string):counter =
    X := counter{Name := N}
    set X.Count = 42
    X

Insert(T:?tree, K:int):tree =
    if (N := T?):
        if (K < N.Key) then tree{Key := N.Key, Left := option{Insert(N.Left, K)}, Right := N.Right}
        else tree{Key := N.Key, Left := N.Left, Right := option{Insert(N.Right, K)}}
    else tree{Key := K}

InOrder(T:?tree):string =
    if (N := T?) then "{InOrder(N.Left)}{N.Key} {InOrder(N.Right)}" else ""

Length(L:?node):int =
    var N:int = 0
    var Cur:?node = L
    loop:
        if (C := Cur?):
            set N += 1
            set Cur = C.Next
        else:
            break
    N

Main():void =
    # aliases see writes, also writes made in a method
    C := counter{Name := "c"}
    D := C
    set C.Count = 10
    Print("{D.Count}")
    Print("{D.Bump()} {C.Count}")
    # a failure context undoes the writes it made
    if (set C.Count = 99, C.Count > 100) then Print("big") else Print("{C.Count}")
    for (X : array{1, 2, 3}, (set C.Count = X * 100; true?), X > 2) { Print("kept {C.Count}") }
    Print("{C.Count}")
    # through a struct and an array: the object is written, not the container
    H := holder{C := C}
    set H.C.Count = 5
    Print("{C.Count} {H.C.Count}")
    Cs := array{counter{Name := "x"}, counter{Name := "y"}}
    if (set Cs[1].Count = 7) {}
    if (Y := Cs[1]) then Print("{Y.Name} {Y.Count}")
    # objects outlive the function that made them
    M := MakeBumped("m")
    Print("{M.Name} {M.Count}")
    # <unique>: identity, not equal fields
    T1 := token{Label := "a"}
    T2 := token{Label := "a"}
    T3 := T1
    if (T1 = T3) then Print("same")
    if (T1 <> T2) then Print("different")
    if (T1 = T2) then Print("wrong") else Print("not equal")
    # recursive classes: a list linked by writing Next, and a tree
    Head := node{Value := 1}
    Second := node{Value := 2}
    set Head.Next = option{Second}
    set Second.Next = option{node{Value := 3}}
    Print("length {Length(option{Head})}")
    var T:?tree = false
    for (K : array{5, 2, 8, 1, 9, 3}) { set T = option{Insert(T, K)} }
    Print(InOrder(T))
