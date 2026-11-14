# expect: expected string, found int
label := class<computes>{}
ToString(L:label)<computes>:int = 7
Main():void = Print("{label{}}")
