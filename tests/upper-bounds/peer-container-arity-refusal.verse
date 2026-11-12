Upper(Base:t,Value:u where t:type,u:subtype(t))<computes>:t=Value
Main():void=
    Base:tuple(rational,string)=(1,"base")
    Value:tuple(int,string,int)=(7,"value",9)
    Upper(Base,Value)
