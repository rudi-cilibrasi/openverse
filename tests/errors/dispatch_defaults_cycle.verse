# expect: uses itself
left(t:type) := interface:
    Get(?N:int=0):int
    Other(?N:int=0):int
leading(t:type) := interface:
    Tag():t
both(a:type,b:type) := class(leading(a),left(b)):
    V:a
    Tag<override>():a=V
    Get<override>(?N:int=block{ P:left(b)=Self; P.Other() }):int=N
    Other<override>(?N:int=block{ P:left(b)=Self; P.Get() }):int=N
Run(P:left(t) where t:type):int=P.Get()
Main():void=Print("{Run(both(int,string){V:=1})}")
