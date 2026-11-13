Upper(Base:t,Value:u where t:type,u:subtype(t))<computes>:t=Value
Main():void=
    Base:[]int=array{}
    Value:[]rational=array{1}
    Upper(Base,Value)
