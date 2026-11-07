# expect: expected int, found string
i1 := interface:
    var F2:int = 15
c := class:
    var O:?i1 = false
    var A:[]i1 = array{}
    var M:[int]i1 = map{}
Main():void =
    X := c{}
    if (set X.A[0].F2 = 7) then Print("set") else Print("empty")
    if (set X.M[3].F2 += 7) then Print("set") else Print("empty")
    if (set X.O?.F2 = "str") then Print("set") else Print("empty")
