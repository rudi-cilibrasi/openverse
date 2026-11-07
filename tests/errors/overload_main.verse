# expect: Main cannot be overloaded
Main(X:int):void = Print("x")
Main():void = Print("x")
