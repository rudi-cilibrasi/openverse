# expect: 2:0: the bound 18446744073709551621 does not fit in 64 bits
huge := type{_X:int where _X > 18446744073709551621}
Main():void = Print("x")
