# expect: <suspends>
Get(X:int)<computes>:int = X + 1
Get(X:string)<suspends>:int = X.Length
Main():void = Print("{Get("word")}")
