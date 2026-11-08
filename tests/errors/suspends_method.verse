# expect: a <suspends> method (c.Run) is not supported yet
c := class:
    Run()<suspends>:void = Sleep(1.0)
Main():void = Print("x")
