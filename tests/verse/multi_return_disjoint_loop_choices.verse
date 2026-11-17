Sources()<computes>:[]int=array{}|array{1}
Pick(Mode:int)<transacts>:int=
    if(Mode=1):
        for(I:Sources()):
            Y:=I|I+10
            return Y
    else:
        for(I:=1..2):
            Y:=I|I+10
            if(I=2):return Y
            Print("advance {I} {Y}")
    99
Main()<transacts>:void=
    for(V:=Pick(1)):Print("header {V}")
    for(V:=Pick(2)):Print("plain {V}")
