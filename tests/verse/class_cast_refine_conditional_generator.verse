pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    Items:[]t = array{}
    C:int = 1
    var Counter:int=0
Condition(P:pair(a, b), N:int where a:type, b:type):[]int =
    for (D := dup[P], X : D.Items, Y := (if (D.C > 0) then (N | 10) else 0)) { Y }
Values(P:pair(a, b), N:int where a:type, b:type):[]a =
    for (D := dup[P], X : D.Items, Y := (if (N > 0) then (D.A | D.B) else D.A)) { Y }
OtherValues(P:pair(a, b), N:int where a:type, b:type):[]b =
    for (D := dup[P], X : D.Items, Y := (if (N > 0) then (D.A | D.B) else D.A)) { Y }
Local(P:pair(a, b), N:int where a:type, b:type):[]int =
    var Count:int=0
    for (D := dup[P], X : D.Items, (set Count=(if (N > 0) then (D.C | 10) else 0);true?), Y:=Count) { Y }
Field(P:pair(a, b), N:int where a:type, b:type):[]int =
    for (D := dup[P], X : D.Items, (set D.Counter=(if (N > 0) then (D.C | 10) else 0);true?), Y:=D.Counter) { Y }
Main():void=
    D:=dup(int){A:=7,B:=8,Items:=array{5,6},C:=2}
    P:pair(int,int)=D
    Print("condition {Condition(P,1).Length} {Condition(P,0).Length}")
    for(V:Values(P,1)):
        Print("value {V}")
    for(V:Values(P,0)):
        Print("else {V}")
    for(V:OtherValues(P,1)):
        Print("other {V}")
    Print("local {Local(P,1).Length} {Local(P,0).Length}")
    for(V:Field(P,1)):
        Print("field {V}")
    Print("counter {D.Counter}")
