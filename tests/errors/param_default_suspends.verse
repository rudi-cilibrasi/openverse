# expect: the default of ?Value of F cannot suspend, also of a <suspends> function
Wait()<suspends>:int = 0
F(?Value:int = Wait())<suspends>:void = {}
Main():void = {}
