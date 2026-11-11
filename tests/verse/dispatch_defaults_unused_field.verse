first(t:type) := interface:
    Tag():t
sink(t:type) := interface:
    F(?N:int=0):int
both(a:type,b:type) := class(first(a),sink(b)):
    V:a
    Tag<override>():a=V
    F<override>(?N:int=block{E:[]b=Concatenate();Print("default ran");E.Length}):int=N
unused := struct:
    N:int=block{P:sink(string)=both(int,string){V:=1};P.F()}
Main()<computes>:void=Print("ok")
