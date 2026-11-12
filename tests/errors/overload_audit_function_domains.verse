# expect: parameters a call cannot tell apart
F(G:type{_(:int)<computes>:int}):int = 1
F(G:type{_(:string)<computes>:string}):int = 2
Main():void = {}
