# two first declarations with different results (a class's and an interface's),
# one override implementing both, called through a dispatch that opens its
# class's type parameters (#209): a cell per declaration
# two roots (class and interface), plain override and qualified ones
expr(t:type) := class<abstract>:
    Copy()<suspends>:expr(t)
    Eval()<suspends>:t
copier(t:type) := interface:
    Copy()<suspends>:copier(t)
pairE(a:type, b:type) := class(expr(tuple(a, b)), copier(tuple(a, b))):
    A:a
    B:b
    Eval<override>()<suspends>:tuple(a, b) = (A, B)
    Copy<override>()<suspends>:pairE(a, b) =
        Sleep(0.1)
        pairE(a, b){A := A, B := B}
Go(E:expr(t) where t:type)<suspends>:t = E.Copy().Eval()
Main()<suspends>:void =
    Y := Go(pairE(int, int){A := 1, B := 2})
    Print("{Y(0)} {Y(1)}")
