# expect: found type{_(:int)<computes>:string}
Id(X:t where t:type)<computes>:t=X
Twice(F:type{_(:t)<computes>:t},X:t where t:type)<computes>:t=F(X)|F(X)
reader:=class:
    Id(X:int)<computes>:string="method {X}"
    Read():[]int=for{Twice(Id,6)}
child:=class(reader):
    Id(X:string)<computes>:int=X.Length
Main():void={}
