# dispatch to classes that fix type arguments, omitting named arguments whose
# defaults have no type of their own: false, array{}, map{} (#175)
box(t:type) := class:
    V:t
    Get(X:t, ?Opt:?int = false, ?Xs:[]t = array{}, ?M:[string]int = map{}):t = V
int_box := class(box(int)):
    Get<override>(X:int, ?Opt:?int = false, ?Xs:[]int = array{}, ?M:[string]int = map{}):int =
        X + (Opt? or 0) + Xs.Length + M.Length
cell := class:
    N:int = 0
cbox := class(box(cell)):
    Get<override>(X:cell, ?Opt:?int = false, ?Xs:[]cell = array{}, ?M:[string]int = map{}):cell = X
G(B:box(t), X:t where t:type):t =
    B.Get(X)
H(B:box(t), X:t where t:type):t =
    B.Get(X, ?Opt := option{5})
Main():void =
    Print("{G(int_box{V := 1}, 10)}")
    Print("{H(int_box{V := 1}, 10)}")
    Print("{G(box(string){V := "s"}, "x")}")
    Print("{G(cbox{V := cell{}}, cell{N := 4}).N}")
