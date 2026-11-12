# Effectful lazy generic edges infer their packed arguments even with a closed result.
Id(X:t where t:type)<computes>:t=X
Empty(?N:int=0 where t:type)<computes>:[]t=array{}
Vals(P:tuple([]t,int) where t:type)<decides>:int=
    P(1)>=0
    Print("visit {P(1)}")
    P(1)|Vals[block{A:[]t=Empty();Id(A)},P(1)-1]
Main():void=if(X:=Vals[array{7},2],X=0){Print("got {X}")}else{Print("none")}
