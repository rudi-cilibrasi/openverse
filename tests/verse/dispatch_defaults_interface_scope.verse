container(t:type) := interface:
    M(?N:int=0):int=N
wrap(u:type) := class(container([]u)):
    M<override>(?N:int=block{ E:[]u=Concatenate(); (super:)M(?N:=E.Length+1) }):int=N
c(t:type) := class(wrap(t)) {}
Get(P:container(a) where a:type):int=P.M()
Main():void=Print("{Get(c(int){})}")
