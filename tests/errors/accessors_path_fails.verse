# expect: Items is a field with accessors whose getter GetItems for this path can fail: use it in a failure context
box := class:
    var Items<getter(GetItems)><setter(SetItems)>:[]int = external{}
    var Data:[]int = array{1}
    GetItems(:accessor)<transacts>:[]int = Data
    GetItems(:accessor, I:int)<transacts><decides>:int = Data[I]
    SetItems(:accessor, V:[]int)<transacts>:void = set Data = V
Main()<transacts>:void =
    B := box{}
    X := B.Items[0]
