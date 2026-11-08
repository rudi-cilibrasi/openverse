# expect: a spawned call whose arguments' types mention the function's type parameters is not supported yet
box(t:type) := class:
    V:t
    Size()<suspends>:int = 0
int_box := class(box(int)):
    Size<override>()<suspends>:int = V
G(B:box(t) where t:type)<suspends>:int =
    T := spawn{B.Size()}
    T.Await()
Main()<suspends>:void = Print("{G(int_box{V := 1})}")
