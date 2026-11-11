# expect: expected type{_(:string):string}, found type{_(:int):int}
box:=class:
    Same(X:t where t:type):t=X
Main():void=
    F:type{_(:int):int}=box{}.Same
    G:type{_(:string):string}=F
    Print("wrong")
