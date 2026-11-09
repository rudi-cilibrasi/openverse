# a spawned dispatch whose implementation calls a generic immediate function
# that spawns, at its type parameters: `$dispatchK` takes the caller's witnesses
# last, so it is copied per type like any such function (#209 review)
cell(t:type) := class<abstract>:
    Get()<suspends>:t
Echo(X:t where t:type)<suspends>:t = X
Kick(X:t where t:type):task(t) = spawn{Echo(X)}
gc(t:type) := class(cell(t)):
    V:t
    Get<override>()<suspends>:t = Kick(V).Await()
Go(C:cell(t) where t:type)<suspends>:t =
    T := spawn{C.Get()}
    T.Await()
Main()<suspends>:void = Print("{Go(gc(int){V := 3})}")
