# a dispatch from pair(t, u) to d, whose pins relate the receiver's type
# arguments to ones dup does not have (#209): refined, as class_exist_relate_beyond
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
