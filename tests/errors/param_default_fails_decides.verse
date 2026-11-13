# expect: the default of ?Value of F can fail: a default is no failure context, also of a <decides> function
Get(Maybe:?int)<transacts><decides>:int = Maybe?
F(?Value:int = Get[option{1}])<transacts><decides>:int = Value
Main():void = {}
