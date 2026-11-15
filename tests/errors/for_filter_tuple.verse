# expect: this filter cannot fail
Main():void=
    X:=1
    Y:=2
    for(I:=0..1,(X,Y)):
        Print("wrong")
