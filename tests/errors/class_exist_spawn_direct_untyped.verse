# expect: an argument of a spawned call of arrJ.Put, a method that reads type arguments from its receiver, must have a type of its own where its parameter's type mentions them
# (Put's X is []a, a read from the receiver: no witness gives a, so the root
# cannot type array{} there; through a variable, E:[]int = array{}, it runs)
job(t:type) := class<abstract>:
    Run()<suspends>:t
    Put(X:t, Y:u where u:type)<suspends>:tuple(u, t)
arrJ(a:type) := class(job([]a)):
    Run<override>()<suspends>:[]a = array{}
    Put<override>(X:[]a, Y:u where u:type)<suspends>:tuple(u, []a) =
        Sleep(0.1)
        (Y, X)
Main()<suspends>:void =
    P := arrJ(int){}
    T := spawn{P.Put(array{}, 1)}
    Print("{T.Await()(0)}")
