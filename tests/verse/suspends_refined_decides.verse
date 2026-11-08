# a refined <decides> method on a receiver kept in the frame: its helper can fail too (#179)
box(t:type) := class:
    V:t
    Pos()<decides>:void = false?
int_box := class(box(int)):
    Pos<override>()<decides>:void = V > 0
G(B:box(t) where t:type)<suspends>:int =
    Sleep(0.1)
    if (B.Pos[]) then 1 else 0
Main()<suspends>:void =
    Print("{G(int_box{V := 4})} {G(int_box{V := -1})} {G(box(string){V := "x"})}")
