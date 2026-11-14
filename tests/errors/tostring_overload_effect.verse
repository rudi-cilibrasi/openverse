# expect: writes
counter := class:
    var Count:int = 0
ToString(C:counter)<transacts>:string =
    set C.Count += 1
    "counter"
Show(C:counter)<computes>:string = "{C}"
Main():void = {}
