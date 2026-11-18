# set O.F.p op= e, past an object's field (#704): the containers in the field
# are resolved before e runs, as a variable's are (set_op_place_replaced), so
# when e replaces the one the last step writes into, or one above it in the
# field, the update goes to the container e replaced, and the field keeps e's.
# Epic's VerseVM, UEFN 43.12 (++Fortnite+Release-43.12-CL-60598086, "Use Verse
# VM", 2026-11-18), prints "field 8 9" for the first case written directly
# (tests/conformance/versevm/compound-object-field-array.verse). The
# replacement is seen through any reference to the object: another name for
# it, a call, another task while e is suspended; a write into the container
# (an element, an append with +=) is not one, nor is a write to another
# object's field. Nested rows compare their keys when they run; a failure
# undoes the watch with the rest; a generic class, an interface's field and a
# module-scoped weak_map's entry follow the same rule.
pair := struct<computes>:
    N:int = 0

cell := class:
    var Arr:[]int = array{1, 2}
    var Grid:[][]int = array{array{1, 2}, array{3, 4}}
    var M:[int]int = map{1 => 10}
    var O:?int = option{3}
    var S:pair = pair{N := 1}

box(t:type) := class:
    var Items:[]t = array{}

holder := interface:
    var Vals:[]int

impl := class(holder):
    var Vals<override>:[]int = array{1, 2}

key := class<unique><module_scoped_var_weak_map_key>:
    Number:int = 0

var Entries:weak_map(key, []int) = map{}

Id(N:int):int = N

Replace(C:cell)<transacts>:int =
    set C.Arr = array{8, 9}
    1

Show(Xs:[]int):string =
    var S:string = ""
    for (I -> X : Xs):
        if (I > 0) then set S += ", "
        set S += ToString(X)
    "[{S}]"

ShowRows(Rows:[][]int):string =
    var S:string = ""
    for (I -> Row : Rows):
        if (I > 0) then set S += " "
        set S += Show(Row)
    "[{S}]"

Later(C:cell)<suspends>:void =
    Sleep(0.1)
    set C.S = pair{N := 50}

Slow()<suspends>:int =
    Sleep(0.5)
    1

Main()<suspends>:void =
    C := cell{}
    D := C
    if (set C.Arr[1] += (set D.Arr = array{8, 9}; 1)) then Print("alias {Show(C.Arr)}")
    set C.Arr = array{1, 2}
    if (set C.Arr[1] += Replace(D)) then Print("call {Show(C.Arr)}")
    set C.Arr = array{1, 2}
    if (set C.Arr[1] += (set D.Arr[1] = 50; 1)) then Print("element in place {Show(C.Arr)}")
    set C.Arr = array{1, 2}
    if (set C.Arr[1] += (set D.Arr += array{7}; 1)) then Print("appended in place {Show(C.Arr)}")
    set C.Arr = array{1, 2}
    Other := cell{}
    if (set C.Arr[1] += (set Other.Arr = array{8, 9}; 1)) then Print("another object {Show(C.Arr)} {Show(Other.Arr)}")
    if (set C.Grid[1][0] += (set D.Grid[Id(1)] = array{9, 9}; 10)) then Print("row replaced {ShowRows(C.Grid)}")
    set C.Grid = array{array{1, 2}, array{3, 4}}
    if (set C.Grid[1][0] += (set D.Grid[Id(0)] = array{5}; 10)) then Print("other row replaced {ShowRows(C.Grid)}")
    set C.Grid = array{array{1, 2}, array{3, 4}}
    if (set C.Grid[1][0] += (set D.Grid = array{array{0}, array{7, 7}}; 10)) then Print("field replaced {ShowRows(C.Grid)}")
    if (set C.M[1] += (set D.M = map{1 => 100}; 1), V := C.M[1]) then Print("map {V}")
    if (set C.O? += (set D.O = option{9}; 1), V := C.O?) then Print("option {V}")
    set C.S.N += (set D.S = pair{N := 50}; 1)
    Print("struct {C.S.N}")
    set C.Arr = array{1, 2}
    if (set C.Arr[1] += (set D.Arr = array{8, 9}; 1), C.Arr.Length = 5) {}
    Print("rolled back {Show(C.Arr)}")
    if (set C.Arr[1] += (set D.Arr[0] = 30; 1)) then Print("after the rollback {Show(C.Arr)}")
    set C.Arr = array{1, 2}
    if (set C.Arr[0] += (if (set C.Arr[1] += (set D.Arr = array{8, 9}; 1)) then 1 else 0)) then Print("nested {Show(C.Arr)}")
    B := box(int){Items := array{1, 2}}
    if (set B.Items[0] += (set B.Items = array{40}; 1)) then Print("generic {Show(B.Items)}")
    I:holder = impl{}
    if (set I.Vals[1] += (set I.Vals = array{8, 9}; 1)) then Print("interface {Show(I.Vals)}")
    K := key{}
    if (set Entries[K] = array{1, 2}, set Entries[K][1] += (set Entries[K] = array{8, 9}; 1), E := Entries[K]):
        Print("module entry {Show(E)}")
    set C.S = pair{N := 1}
    spawn{Later(C)}
    set C.S.N += Slow()
    Print("another task {C.S.N}")
