# a refined dispatch (#142) of an immediate method in a suspends function, on a receiver kept in the frame (#179)
box(t:type) := class:
    V:t
    Size():int = 0
int_box := class(box(int)):
    Size<override>():int = V
G(B:box(t) where t:type)<suspends>:int =
    Sleep(1.0)
    B.Size()
Main()<suspends>:void = Print("{G(int_box{V := 4})} {G(box(string){V := "x"})}")
