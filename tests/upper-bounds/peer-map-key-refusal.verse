Upper(Base:t,Value:u where t:type,u:subtype(t))<computes>:t=Value
Main():void=
    Base:[int]rational=map{}
    Value:[rational]int=map{}
    Upper(Base,Value)
