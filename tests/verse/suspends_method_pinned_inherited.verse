# a class that fixes the type argument but inherits the generic
# implementation: that call needs no refinement (#171)
box(t:type) := class:
    V:t
    Get()<suspends>:t = V
    Peek()<suspends>:t = V
int_box := class(box(int)):
    Peek<override>()<suspends>:int = V + 1
str_box := class(box(string)):
    Get<override>()<suspends>:string = "{V}!"
G(B:box(t) where t:type)<suspends>:t = B.Peek()
Main()<suspends>:void = Print(G(str_box{V := "s"}))
