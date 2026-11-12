# expect: must be comparable
bad:=class{}
F(P:tuple(t,t) where t:subtype(comparable)):int=1
Main():void=Print("{F(bad{},bad{})}")
