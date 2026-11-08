# a generic immediate method that spawns a call of closed types (#174)
Worker()<suspends>:int =
    Sleep(1.0)
    7
box(t:type) := class:
    V:t
    Start():task(int) = spawn{Worker()}
Main()<suspends>:void =
    B := box(string){V := "s"}
    Print("{B.Start().Await()}")
