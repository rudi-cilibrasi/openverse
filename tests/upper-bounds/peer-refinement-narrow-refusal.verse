small:=type{_X:int where 0 <= _X, _X <= 10}
wide:=type{_X:int where -10 <= _X, _X <= 20}
Upper(Base:t,Value:u where t:type,u:subtype(t))<computes>:t=Value
Main():void=
    Base:small=0
    Value:wide=7
    Upper(Base,Value)
