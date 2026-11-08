# every class below pairish repeats its type arguments: dispatch through
# a field of an interface type refines them (#157, #209)
pairish(t:type, u:type) := interface:
    Left():t
    Right():u
rep(t:type) := class(pairish(t, t)):
    V:t
    Left<override>():t = V
    Right<override>():t = V
holder(t:type, u:type) := class:
    P:pairish(t, u)
LeftOf(H:holder(t, u) where t:type, u:type):t = H.P.Left()
Main():void =
    H:holder(int, int) = holder(int, int){P := rep(int){V := 9}}
    Print("{LeftOf(H)} {H.P.Right()}")
