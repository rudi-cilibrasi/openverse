# Empty tuple fields take the method type inferred from the final field.
base := class:
    Values(E:[]t,O:?t,M:[string]t,X:t,?Last:?t=false where t:type)<transacts>:tuple(int,int,t) =
        (E.Length,M.Length,X)|(E.Length+1,M.Length+1,if(V:=Last?)then V else X)
child := class(base):
    Values<override>(E:[]u,O:?u,M:[string]u,X:u,?Last:?u=false where u:type)<transacts>:tuple(int,int,u) =
        (E.Length+2,M.Length+2,if(V:=Last?)then V else X)|(super:)Values((E,O,M,X),?Last:=Last)
solo := class:
    Alone(E:[]v,O:?v,M:[string]v,X:v where v:type)<transacts>:tuple(int,int,v) =
        (E.Length,M.Length,X)|(E.Length+1,M.Length+1,X)
Args(X:w where w:type)<transacts>:tuple([]w,?w,[string]w,w) =
    Print("args")
    (array{},false,map{},X)
Main():void =
    B:base=child{}
    for(V:=B.Values((array{},false,map{},"s"),?Last:=option{"z"})): Print("literal {V(0)} {V(1)} {V(2)}")
    for(V:=B.Values(Args("p"),?Last:=option{"q"})): Print("computed {V(0)} {V(1)} {V(2)}")
    for(V:=solo{}.Alone((array{},false,map{},7))): Print("direct {V(0)} {V(1)} {V(2)}")
