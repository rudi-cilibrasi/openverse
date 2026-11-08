# formerly refused: a spawned dispatch refined by #142 in a generic function, now specialised (#174)
box(t:type) := class:
    V:t
    Size()<suspends>:int = 0
int_box := class(box(int)):
    Size<override>()<suspends>:int = V
G(B:box(t) where t:type)<suspends>:int =
    T := spawn{B.Size()}
    T.Await()
Main()<suspends>:void = Print("{G(int_box{V := 1})}")
