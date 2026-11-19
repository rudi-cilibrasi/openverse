# expect: using a value of type type{_(:int):int} as a value of type type{_(:int):void} is not yet implemented
# (#724) a local of type type{_(:int):int} used as a type{_(:int):void}, its
# result discarded: a wrapper (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, error 3502, "Using a value of type
# int->int as a value of type int->void": followup-coerce2/value-void-result).
# IntIdentity named there is admitted (fn_coerce_named_void).
IntIdentity(X:int):int = X
Run(F(:int):void):void = F(1)
Main():void =
    G:type{_(:int):int} = IntIdentity
    Run(G)
