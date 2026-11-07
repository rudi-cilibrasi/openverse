# expect: no operator '+' for t and t
# A generic body is checked once, even when the function is never called.
Double(X:t where t:type):t = X + X

Main():void = Print("never called")
