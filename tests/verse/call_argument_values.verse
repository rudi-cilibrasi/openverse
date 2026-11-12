# The pre-elaboration inliner and recursive binder share call packing.
PairValues(P:tuple(int,int)):int=P(0)|P(1)
UnitValues(P:tuple()):int=7|8
OneValues(P:tuple(int)):int=P(0)|-P(0)
GenericValues(P:t where t:type):t=P|P
ArrayValues(P:[]t where t:type):int=P.Length|0
Recur(P:tuple(int,int))<computes><decides>:int=
    P(0)<=P(1)
    P(0)|Recur[P(0)+1,P(1)]
Main():void=
    for(X:=PairValues(1,2)){Print("pair {X}")}
    for(X:=UnitValues()){Print("unit {X}")}
    for(X:=OneValues(3)){Print("one {X}")}
    for(X:=GenericValues(4,"five")){Print("generic {X(0)} {X(1)}")}
    for(X:=ArrayValues(6,7)){Print("array {X}")}
    for(X:=Recur[8,9]){Print("recursive {X}")}
