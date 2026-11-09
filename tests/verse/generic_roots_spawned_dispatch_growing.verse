# a spawned dispatch in a function that calls itself at ever bigger types: the
# dispatch is a generic `$dispatchK`, so no copy per type is needed (#209)
cell(t:type) := class<abstract>:
    Get()<suspends>:t
icell := class(cell(int)):
    Get<override>()<suspends>:int = 1
anycell(t:type) := class(cell(t)):
    V:t
    Get<override>()<suspends>:t = V
Grow(C:cell(t), N:int where t:type)<suspends>:int =
    T := spawn{C.Get()}
    T.Await()
    if (N > 0) then Grow(anycell([]t){V := array{}}, N - 1) else 0
Main()<suspends>:void = Print("{Grow(icell{}, 3)}")
