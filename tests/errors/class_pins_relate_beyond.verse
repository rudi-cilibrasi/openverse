# expect: cannot dispatch Get on a pair(t, u) to class d yet
pair(t:type, u:type) := class:
    A:t
    B:u
    Get():t = A
dup(t:type) := class(pair(t, t)):
    Get<override>():t = B
p(t:type, w:type) := class(dup(t)):
    W:w
    Name():string = "p"
d(w:type) := class(p(?w, w)):
    Name<override>():string = "d"
First(P:pair(t, u) where t:type, u:type):t = P.Get()
Main():void =
    if (X := First(d(int){A := false, B := option{1}, W := 2})?) then Print("{X}")
