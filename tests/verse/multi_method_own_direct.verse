# Receiver and method type parameters have independent instances.
solo(t:type) := class:
    Value:t
    var Count:int=0
    Both(X:u,?Y:u=X,?E:[]u=array{X},?Pair:tuple(t,u)=(Value,X) where u:type)<transacts>:tuple(t,u) =
        Print("both {E.Length}")
        Pair|(Value,Y)
    Repeat(X:v,N:int where v:type)<transacts><decides>:tuple(t,v,int) =
        N>=0
        set Count+=1
        Print("visit {N}")
        (Value,X,N)|Self.Repeat[(X,N-1)]
All(B:solo(a),X:b,Y:b where a:type,b:type):[]tuple(a,b) =
    for(V:=B.Both(X,?Y:=Y)): V
First(B:solo(a),X:b,W:w where a:type,b:type,w:type):?tuple(a,b,int) =
    option{V:=B.Repeat[X,2], E:[]w=Concatenate(), V(2)=0, V}
Main():void =
    I:=solo(int){Value:=7}
    for(V:All(I,"x","y")): Print("all {V(0)} {V(1)}")
    S:=solo(string){Value:="s"}
    if(V:=First(S,9,option{7})?)then Print("first {V(0)} {V(1)} {V(2)}")
    Print("count {S.Count}")
