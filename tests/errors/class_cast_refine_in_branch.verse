# expect: which a cast gives only as a clause of a failure context
# (#243) a refining cast inside a branch of an if that is an expression,
# which lifting it out of the if would evaluate whichever branch runs:
# write it as a clause of a block there, (D := dup[P]; D.C)
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    C:int = 4
Br(P:pair(a, b), N:int where a:type, b:type):?int = option{X := (if (N > 0) then dup[P].C else 0); X + 1}
Main():void = if (V := Br(dup(int){A := 1, B := 2}, 1)?) then Print("{V}")
