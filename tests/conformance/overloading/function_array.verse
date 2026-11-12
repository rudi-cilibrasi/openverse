F(X:[]int):string="array"
F(X:type{_(:int)<decides>:int}):string="function"
Main():void=Print(F(array{1,2}))
