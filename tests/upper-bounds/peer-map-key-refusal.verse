Upper(Base:t,Value:u where t:type,u:subtype(t))<computes>:t=Value
Main():void=
    Base:[rational]rational=map{}
    Value:[int]int=map{}
    Upper(Base,Value)
