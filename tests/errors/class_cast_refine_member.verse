# expect: which a cast gives only as a clause of a failure context
# (#243) a refining cast inside an expression, here a member's receiver, is
# refused: bind it as a clause, D := dup[P], whose rest is then its branch
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    C:int = 4
Use(P:pair(a, b) where a:type, b:type)<decides>:int = dup[P].C
Main():void = if (V := Use[dup(int){A := 1, B := 2}]) then Print("{V}")
