# expect: unknown identifier 'Undefined'
i1 := interface:
    var F2:int = 15
c := class:
    var A:[]i1 = array{}
Main():void =
    X := c{}
    if (set X.A[0].F2 = Undefined) then Print("set") else Print("empty")
