# expect: the arguments of a spawned call cannot suspend
Wait()<suspends>:int=block{Sleep(0.01);1}
F(P:tuple(int,int))<suspends>:void=Sleep(Inf)
Main()<suspends>:void=
    T:=spawn{F(Wait(),2)}
    T.Cancel()
