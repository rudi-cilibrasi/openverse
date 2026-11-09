# a subclass that implements a plain interface while fixing the type parameter
# that interface does not give: the root does not count it, its pins give the
# argument, so the root keeps it as given (spawns and copies stay allowed, #276)
Worker()<suspends>:int =
    Sleep(0.1)
    7
shower := interface:
    Show():string
starter(t:type) := interface:
    Start():task(int)
box(t:type) := class(starter(t)):
    V:t
    Start<override>():task(int) = spawn{Worker()}
ibox := class(box(int), shower):
    Show<override>():string = "ibox {V}"
Main()<suspends>:void =
    S:shower = ibox{V := 3}
    Print(S.Show())
    B:starter(string) = box(string){V := "x"}
    Print("{B.Start().Await()}")
