# expect: 2:0: F has more than one of <converges>, <computes> and <transacts> (they exclude each other)
F()<converges><transacts>:void = Print("x")
G()<computes><converges>:int = 1
Main():void = F()
