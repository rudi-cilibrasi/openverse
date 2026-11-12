# expect: has overloads of F a call cannot tell apart
i(t:subtype(comparable)):=interface:
    F(P:tuple(t))<computes>:string
    F(P:[logic]t)<computes>:string
Main():void={}
