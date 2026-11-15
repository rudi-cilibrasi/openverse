base:=class:
    Values()<computes>:int=3|6
    Values(X:int)<computes>:int=X+3
derived:=class(base):
    Values<override>()<computes>:int=103|(super:)Values()
Main():void=
    var Count:int=0
    for(base{}.Values()<>derived{}.Values(),(set Count+=1;true?)):
        Print("for {Count}")
    Print("after {Count}")
    if(Value:=first{base{}.Values()<>derived{}.Values();(set Count+=1;true?);Count}):
        Print("first {Value}, after {Count}")
