# expect: an array index must be an int, found tuple(int)
Single(P:tuple(u) where u:type)<computes>:tuple(u)=P
Main():void=
    Wrap:type{_(:int)<computes>:tuple(int)}=Single
    A:[]int=array{1}
    if(X:=A[Wrap(0)]){Print("{X}")}
