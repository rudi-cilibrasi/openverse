# a class below existential ones, made at its parent's type directly: its
# object goes through a temporary of its own type (#209)
ex(t:type) := class<abstract>:
    Eval():t
cst(t:type) := class(ex(t)):
    V:t
    Eval<override>():t = V
w1(a:type) := class(ex([]a)):
    E:ex(a)
    Eval<override>():[]a = array{E.Eval()}
w2(b:type) := class(w1(?b)):
    G:int = 0
w3 := class(w2(int)):
    Q:int = 0
Main():void =
    O:ex([]?int) = w3{E := cst(?int){V := false}}
    Print("{O.Eval().Length}")
