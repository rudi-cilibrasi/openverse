small:=type{_X:int where 0 <= _X, _X <= 10}
Upper(Base:t,Value:u where t:type,u:subtype(t))<computes>:t=Value
Main():void=
    Base:small=0
    Value:int=7
    Upper(Base,Value)
