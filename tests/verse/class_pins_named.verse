# a named argument in a call dispatched to a class that fixes type arguments (#142, review of #155)
box(t:type) := class:
    V:t
    Get(?K:int = 0):t = V
int_box := class(box(int)):
    Get<override>(?K:int = 0):int = V + K
G(B:box(t) where t:type):t = B.Get(?K := 5)
Main():void =
    Print("{G(int_box{V := 1})}")
    Print("{G(box(int){V := 2})}")
