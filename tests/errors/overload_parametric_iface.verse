# expect: Show is defined twice with parameters a call cannot tell apart, (pi(int)) and (pi(string))
pi(t:type) := interface:
    Q:int = 0
c := class(pi(string), pi(int)):
    Z:int = 1
Show(X:pi(int)):string = "int"
Show(X:pi(string)):string = "string"
Main():void =
    Print(Show(c{}))
    X:pi(string) = c{}
    Print(Show(X))
