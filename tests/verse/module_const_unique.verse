# A module constant N:c = c{} of a <unique> class without fields is one
# object, the same at every use (#724): the program starts with it, as with
# its classes' prototypes (the Book's tests, GlobalVariables.versetest 72 to
# 74; Epic's compiler and Verse VM, UEFN 43.12,
# followup-refused/module-const-unique: same and different). An empty map{},
# array{} or false holds no object, whatever its type
# (followup-refused/module-const-empty-map-unique-key: length 0).
u := class<unique><allocates><computes>{}
v := class<unique><allocates><computes>(u){}
m := module:
    Inner<public>:u = u{}
Instance1:u = u{}
Instance2:u = u{}
V1:v = v{}
Empty:[u]int = map{}
None:?u = false
Arr:[]u = array{}

holder := class<allocates>:
    F:u = Instance1

Get()<transacts>:u = Instance1

Main():void =
    if (Instance1 = Instance1, Instance1 <> Instance2, Get() = Instance1, Get() <> Instance2):
        Print("same and different")
    if (m.Inner = m.Inner, m.Inner <> Instance1). Print("a module's own")
    if (V1 = V1, K:u = V1, K <> Instance1). Print("of a class below")
    M := map{Instance1 => 1, Instance2 => 2}
    if (M[Instance1] = 1, M[Instance2] = 2, M[Get()] = 1). Print("keys {M.Length}")
    Fresh := u{}
    if (Fresh <> Instance1, Fresh <> Instance2). Print("a new object is another")
    if (v[Instance1]) then Print("wrong") else Print("not a v")
    A := holder{}
    B := holder{}
    if (A.F = B.F, A.F = Instance1). Print("shared by defaults")
    # a failure context that fails leaves it the same object
    var Seen:[u]int = map{}
    if (set Seen[Instance1] = 1, set Seen[Get()] = 2). Print("seen {Seen.Length}")
    if (set Seen[Instance2] = 3, false?) then Print("no") else Print("rolled back {Seen.Length}")
    if (Instance1 = Get(), Seen[Instance1] = 2). Print("same after rollback")
    Print("{Empty.Length} {Arr.Length}")
    if (not None?). Print("none")
