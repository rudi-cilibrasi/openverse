Same(X:u where t:subtype(int),u:subtype(t))<computes>:u=
    if(X=X)then X else Err()
Main():void=
    R:=Same(7)
    Print("{R}")
