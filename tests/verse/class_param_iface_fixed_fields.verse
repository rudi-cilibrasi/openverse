# the same with a fixed type argument, and fields (#276)
shower := interface:
    Show():string
container(t:type) := interface:
    Get():t
box(t:type) := class(container(t)):
    V:t
    Get<override>():t = V
    Both():[]t = array{V, Get()}
ibox := class(box(int), shower):
    Show<override>():string = "ibox {Get()} {Both().Length}"
Main():void =
    S:shower = ibox{V := 4}
    Print(S.Show())
    C:container(int) = ibox{V := 5}
    Print("{C.Get()}")
    C2:container(string) = box(string){V := "x"}
    Print(C2.Get())
