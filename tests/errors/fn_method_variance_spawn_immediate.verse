# expect: takes a call of a <suspends> function
box(t:type):=class:
    V:t
    Code()<computes>:int=7
Main():void=
    F:type{_()<computes>:rational}=box(string){V:="tag"}.Code
    T:=spawn{F()}
