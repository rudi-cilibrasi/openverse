# a copy at a type that rules out a class fixing type arguments drops that class's refined test (#174)
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
