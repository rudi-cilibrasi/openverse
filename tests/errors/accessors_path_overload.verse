# expect: Items is a field with accessors: this read calls its getter GetItems with 1 argument(s) after the accessor
box := class:
    var Items<getter(GetItems)><setter(SetItems)>:[]int = external{}
    var Data:[]int = array{1}
    GetItems(:accessor)<transacts>:[]int = Data
    SetItems(:accessor, V:[]int)<transacts>:void = set Data = V
Main()<transacts><decides>:void =
    B := box{}
    X := B.Items[0]
