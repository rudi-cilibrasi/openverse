# expect: using a value of type type{_(?A:int = …):int} as a value of type type{_():int} is not yet implemented
# (#724) a local bound to F2, whose only parameter is named and defaulted,
# passed where a type{_():int} is expected (F2 named there is admitted,
# fn_coerce_named_default_control): refused (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, error 3502,
# "Using a value of type (?A:int = ...)->int as a value of type tuple()->int":
# followup-coerce/value-default-drop).
F2(?A:int = 2):int = A
Call(F():int):int = F()
Main():void =
    G := F2
    Print("{Call(G)}")
