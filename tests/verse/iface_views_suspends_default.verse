# A <suspends> interface default reached through a view that is a compound
# of the class's type arguments (sink([]u)), from generic code, with a class
# below that overrides it (#351): the frame's type arguments are the
# caller's, written back from the types the dispatch binds them to
container(t:type) := interface:
    Get():t
sink(u:type) := interface:
    Put(X:u)<suspends>:string = "sink"
both(t:type, u:type) := class(container(t), sink([]u)):
    V:t
    Get<override>():t = V
ib(u:type) := class(both(int, u)):
    Put<override>(X:[]u)<suspends>:string = "ib"
G(S:sink(x), V:x where x:type)<suspends>:string = S.Put(V)
Main()<suspends>:void =
    Print(G(both(int, string){V := 1}, array{"a"}))
    Print(G(ib(string){V := 2}, array{"b"}))
    T := spawn{G(both(char, int){V := 'c'}, array{1})}
    Print(T.Await())
