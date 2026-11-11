# expect: the arguments of a spawned call cannot suspend
base(t:type) := class { Go()<suspends>:void=Print("base") }
ib := class(base(int)) { Go<override>()<suspends>:void=Sleep(0.01) }
Make()<suspends>:base(int)=ib{}
Main():void=
    T:=spawn{Make().Go()}
    Print("bad")
