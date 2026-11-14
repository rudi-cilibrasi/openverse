# expect: GetItems takes 1 argument(s), found 0
box := class:
    var Items<getter(GetItems)><setter(SetItems)>:[]int = external{}
    var Data:[]int = array{1}
    GetItems(:accessor)<transacts>:[]int = Data
    SetItems(:accessor, V:[]int)<transacts>:void = set Data = V
    Peek()<transacts>:[]int = GetItems()
Main():void = {}
