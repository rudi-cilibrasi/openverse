# Paths into a field with accessors' value (Book of Verse tests,
# DeepMutabilityForCustomClassVarAccessors.versetest): one call of the getter or
# setter that takes the path's indices and field names; a path that is not
# into a value (.Length) reads the field first.
pair := struct:
    A:int = 1
    B:[]int = array{10, 20}

box := class:
    var P<getter(GetP)><setter(SetP)>:pair = external{}
    var Items<getter(GetItems)><setter(SetItems)>:[]int = external{}
    var Data:pair = pair{}
    var ItemsData:[]int = array{1, 2, 3}
    GetP(:accessor)<transacts>:pair =
        Print("GetP")
        Data
    GetP(:accessor, F:[]char)<transacts><decides>:int =
        Print("GetP {F}")
        if (F = "A") then Data.A else Err()
    GetP(:accessor, F:[]char, I:int)<transacts><decides>:int =
        Print("GetP {F}[{I}]")
        Data.B[I]
    SetP(:accessor, V:pair)<transacts>:void =
        Print("SetP")
        set Data = V
    SetP(:accessor, F:[]char, V:int)<transacts><decides>:void =
        Print("SetP {F}")
        set Data = pair{A := V, B := Data.B}
    SetP(:accessor, F:[]char, I:int, V:int)<transacts><decides>:void =
        Print("SetP {F}[{I}]")
        set Data = pair{A := Data.A, B := array{V, Data.B[1]}}
    GetItems(:accessor)<transacts>:[]int =
        Print("GetItems")
        ItemsData
    GetItems(:accessor, I:int)<transacts><decides>:int =
        Print("GetItems[{I}]")
        ItemsData[I]
    SetItems(:accessor, V:[]int)<transacts>:void =
        Print("SetItems")
        set ItemsData = V
    SetItems(:accessor, I:int, V:int)<transacts><decides>:void =
        Print("SetItems[{I}]")
        set ItemsData[I] = V

Main()<transacts>:void =
    O := box{}
    Print(ToString(O.Items.Length))
    if (X := O.Items[1]):
        Print(ToString(X))
    if (set O.Items[2] = 30):
        Print(ToString(O.Items.Length))
    if (not (set O.Items[9] = 1)):
        Print("out of range")
    if (A := O.P.A):
        Print(ToString(A))
    if (set O.P.A = 5, B := O.P.B[0]):
        Print(ToString(B))
    if (set O.P.B[0] = 7, C := O.P.B[0]):
        Print(ToString(C))
    set O.Items += array{4}
    Print(ToString(O.Items.Length))
