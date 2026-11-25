# expect: using a value of type type{_(:int):int} as a value of type type{_(:int):rational} is not yet implemented: a function value that is no function named
# (#724) a local of type type{_(:int):int} used as a type{_(:int):rational}:
# a function named there is a value of it (#214), a function value needs a
# wrapper (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, error 3502, "Using a value of type int->int as a value
# of type int->rational": followup-coerce2/value-int-rational-result).
Twice(X:int):int = 2 * X
Run(F(:int):rational):int = Floor(F(3))
Main():void =
    G:type{_(:int):int} = Twice
    Print("{Run(G)}")
