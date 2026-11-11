box(t:type) := class:
    Mix(A:t,B:[]t,?D:[]t=Concatenate()):int = B.Length + D.Length | B.Length + D.Length + 1
fixed := class(box(int)):
    Mix<override>(A:int,B:[]int,?D:[]int=Concatenate()):int = A + B.Length + D.Length | A + B.Length + D.Length + 100
extra(t:type,u:type) := class(box(t)):
    X:u
    Mix<override>(A:t,B:[]t,?D:[]t=Concatenate()):int = B.Length + D.Length | B.Length + D.Length + 2
Run(P:box(t),A:t where t:type):[]int = for (V:=P.Mix((A,array{}))) { V }
Main():void =
    for (V : Run(fixed{},7)) { Print("f {V}") }
    for (V : Run(box(string){},"s")) { Print("b {V}") }
    for (V : Run(extra(string,int){X:=1},"s")) { Print("e {V}") }
    for (V := fixed{}.Mix(7,array{},?D:=array{8,9})) { Print("n {V}") }
