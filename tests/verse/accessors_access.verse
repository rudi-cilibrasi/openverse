# A field with accessors is used with its own access, whatever its accessors'
# (Book of Verse tests, FORT-976754: a <public> field, <private> accessors); a
# parametric class's; a set undone with its failure context.
store := module:
    item<public> := class:
        var Price<public><getter(GetPrice)><setter(SetPrice)>:int = external{}
        var Cents<private>:int = 100
        GetPrice<private>(:accessor)<transacts>:int = Quotient[Cents, 100] or 0
        SetPrice<private>(:accessor, V:int)<transacts>:void = set Cents = V * 100

cell(t:type) := class:
    var Value<getter(GetValue)><setter(SetValue)>:t = external{}
    var Held:?t = false
    GetValue(:accessor)<transacts>:t = Held? or Err()
    SetValue(:accessor, V:t)<transacts>:void = set Held = option{V}

Main()<transacts>:void =
    I := store.item{Price := 3}
    Print(ToString(I.Price))
    set I.Price *= 4
    Print(ToString(I.Price))
    C := cell(string){Value := "x"}
    set C.Value = C.Value + "y"
    Print(C.Value)
    if (set I.Price = 99, I.Price < 50):
        Print("no")
    Print(ToString(I.Price))
