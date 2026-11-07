# expect: '=' compares values of different types, t and u
Same(X:t, Y:u where t:subtype(comparable), u:subtype(comparable))<decides>:void = X = Y
Main():void = Print("x")
