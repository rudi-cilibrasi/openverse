# Fields with accessors (Book of Verse ch. 10, "Fields with Accessors"): a
# read of the field is a call of its getter, a `set` one of its setter; a
# construction calls the setters of the fields it gives, after the stored
# fields have their values (each value evaluated where its field is
# declared) and before the `block:` clauses.
entity := class:
    var Health<getter(GetHealth)><setter(SetHealth)>:int = external{}
    var InternalHealth:int = 100
    GetHealth(:accessor)<transacts>:int = InternalHealth
    SetHealth(:accessor, NewValue:int)<transacts>:void =
        if (NewValue >= 0, NewValue <= 100):
            set InternalHealth = NewValue

counter := class:
    var Count<getter(GetCount)><setter(SetCount)>:int = external{}
    var Limit<getter(GetLimit)><setter(SetLimit)>:int
    var Stored:int = 0
    var Max:int = 100
    var Log:string = ""
    block:
        set Log = Log + "block "
    GetCount(:accessor)<transacts>:int = Stored
    SetCount(:accessor, V:int)<transacts>:void =
        set Log = Log + "SetCount({V}) "
        set Stored = Min(V, Max)
    GetLimit(:accessor)<transacts>:int = Max
    SetLimit(:accessor, V:int)<transacts>:void =
        set Log = Log + "SetLimit({V}) "
        set Max = V

Note(S:string):int =
    Print(S)
    0

Main()<transacts>:void =
    E := entity{}
    Print(ToString(E.Health))
    set E.Health = 42
    Print(ToString(E.Health))
    set E.Health = 500
    Print(ToString(E.Health))
    set E.Health += 8
    Print(ToString(E.Health))
    F := entity{Health := 7}
    Print(ToString(F.Health))
    Y := set F.Health = 9
    Print(ToString(Y))
    A := counter{Limit := 10}
    Print("{A.Log}: {A.Count} of {A.Limit}")
    B := counter{Count := 50 + Note("count"), Max := Note("max") + 20, Limit := 30}
    Print("{B.Log}: {B.Count} of {B.Limit}")
    if (set B.Count = 7, B.Count > 100):
        Print("not here")
    Print("{B.Count}")
