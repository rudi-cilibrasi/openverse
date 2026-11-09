# expect: more than 500 copies of generic functions with a spawned dispatch or an immediate spawn
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
