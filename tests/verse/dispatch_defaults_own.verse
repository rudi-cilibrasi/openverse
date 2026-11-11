Note(N:int)<transacts>:int=
    Print("own {N}")
    N
base(a:type) := class:
    F(?X:t=7 where t:type)<transacts>:int=1
ib := class(base(int)):
    Seed:int=3
    F<override>(?X:u=Note(Seed) where u:type)<transacts>:int=2
Run(P:base(a) where a:type)<transacts>:int=P.F()
Main()<transacts>:void=Print("{Run(ib{})}")
