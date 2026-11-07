# expect: 2:0: NaN cannot bound a refinement
b := type{_X:float where _X < NaN}
Main():void = Print("x")
