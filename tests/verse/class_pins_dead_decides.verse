# a failable call that no class can receive still counts as failable (#142, review of #155)
box(t:type) := class<abstract>:
    V:t
    Try()<decides>:t = V
int_box := class(box(int)):
    Try<override>()<decides>:int =
        V > 0
        V
F(B:box(string), D:string):string = if (X := B.Try[]) then X else D
Main():void = Print("x")
