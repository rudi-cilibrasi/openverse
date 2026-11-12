# expect: has overloads of
# qualified overloads of a parametric interface (#125)
ip(t:type) := interface:
    Get(X:t):string
    Get(X:int, Y:t):string
iq(t:type) := interface:
    Get(X:t):string
c(t:type) := class(ip(t), iq(t)):
    (ip:)Get<override>(X:t):string = "ip one"
    (ip:)Get<override>(X:int, Y:t):string = "ip two {X}"
    (iq:)Get<override>(X:t):string = "iq one"
Main():void =
    C := c(string){}
    A:ip(string) = C
    Print(A.Get("a"))
    Print(A.Get(1, "b"))
    B:iq(string) = C
    Print(B.Get("c"))
    Print(C.(ip:)Get(2, "d"))
    Print(C.(iq:)Get("e"))
