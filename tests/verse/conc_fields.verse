# tasks and events kept in class fields (prototypes of classes whose fields
# refer to classes without one), spawned calls of literals without types of
# their own (#156, review of #158)
H(A:[]int)<suspends>:int =
    Sleep(0.1)
    A.Length
G(O:?int)<suspends>:int =
    Sleep(0.1)
    if (X := O?) then X else 0
Q()<suspends>:int = 1
holder := class:
    Ev:event(int)
    T:task(int)
cell(t:type) := class:
    var V:?t = false
keep := class:
    C:cell(int)
plain := class:
    N:int = 0
uses := class:
    X:plain
Main()<suspends>:void =
    Z := spawn{H(array{})}
    Y := spawn{G(false)}
    Print("h {Z.Await()} g {Y.Await()}")
    B := holder{Ev := event(int){}, T := spawn{Q()}}
    B.Ev.Signal(1)
    Print("{B.T.Await()} {uses{X := plain{}}.X.N}")
