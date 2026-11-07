# expect: F is defined twice with parameters a call cannot tell apart, ([]int) and (string)
F(A:[]int):int = 0
F(S:string):int = 1
Main():void = Print("x")
