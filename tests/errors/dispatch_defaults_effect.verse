# expect: effect <writes>
base(t:type) := class:
    F(?N:int=0)<computes>:int=N
ib := class(base(int)):
    var Seed:int=3
    F<override>(?N:int=block{ set Seed+=1; Seed })<computes>:int=N
Run(P:base(a) where a:type)<computes>:int=P.F()
Main()<transacts>:void=Print("{Run(ib{})}")
