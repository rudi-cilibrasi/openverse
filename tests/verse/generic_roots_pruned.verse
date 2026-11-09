# a spawned dispatch in a generic function, called at a type that rules out a
# class fixing type arguments: compiled once, its refined test kept and never
# passed (until #209, a copy per type dropped it, #174)
# spawn of dispatch in generic function, called at int (refined) and string
box(t:type) := class:
    V:t
    Size()<suspends>:int = 0
int_box := class(box(int)):
    Size<override>()<suspends>:int = V
G(B:box(t) where t:type)<suspends>:int =
    T := spawn{B.Size()}
    T.Await()
Main()<suspends>:void =
    Print("{G(int_box{V := 1})}")
    Print("{G(box(string){V := "x"})}")
    Print("{G(box(int){V := 5})}")
