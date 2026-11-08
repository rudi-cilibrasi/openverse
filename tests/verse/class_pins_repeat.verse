# a class that repeats its parent's type arguments overrides its methods:
# dispatch is typed under the refinement that unifies them (#157, #209)
pair(t:type, u:type) := class:
    A:t
    B:u
    Get():t = A
    Name():string = "pair"
dup(t:type) := class(pair(t, t)):
    Get<override>():t = B
    Name<override>():string = "dup"
dupint := class(dup(int)):
    Get<override>():int = A + B
    Name<override>():string = "dupint"
First(P:pair(t, u) where t:type, u:type):t = P.Get()
# no instance of pair([]x, x) agrees with dup's pins (the occurs check)
Nest(P:pair([]x, x) where x:type):int = P.Get().Length
Main():void =
    Ps:[]pair(int, int) = array{pair(int, int){A := 1, B := 2}, dup(int){A := 3, B := 4}, dupint{A := 5, B := 6}}
    for (P : Ps):
        Print("{P.Name()} {First(P)} {P.Get()}")
    Print("{Nest(pair([]int, int){A := array{1, 2, 3}, B := 0})}")
