# expect: the arguments of a spawned call cannot suspend
box(t:type):=class:
    V:t
    Later()<suspends>:int=block{Sleep(0.0);7}
Make(B:box(t) where t:type)<suspends>:type{_()<suspends>:rational}=
    Sleep(0.0)
    B.Later
Main()<suspends>:void=
    T:=spawn{Make(box(string){V:="tag"})()}
