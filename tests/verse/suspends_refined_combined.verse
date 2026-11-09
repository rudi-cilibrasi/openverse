# a refined call on a receiver read from a field, in a generic suspends function, with placeholders (#179, #174, #157)
expr(t:type) := class<abstract>:
    Eval():t
int_lit := class(expr(int)):
    N:int
    Eval<override>():int = N
holder(t:type) := class:
    E:expr(t)
Watch(Hs:[]holder(t), X:t where t:type)<suspends>:t =
    branch:
        Sleep(0.5)
        Print("tick")
    var R:t = X
    for (H : Hs):
        Sleep(0.3)
        set R = H.E.Eval()
    R
Main()<suspends>:void = Print("{Watch(array{holder(int){E := int_lit{N := 5}}, holder(int){E := int_lit{N := 6}}}, 0)}")
