# expect: must be comparable
box:=class:
    Same(X:t where t:type)<transacts>:t=X
    Compare(X:t,Y:t where t:subtype(comparable))<decides>:t=block{X=Y;X}
Run(X:u where u:type)<transacts><decides>:void=
    F:type{_(:u)<transacts>:u}=box{}.Same
    F(X)=X
Main():void=
    if(Run[3])then Print("wrong")
