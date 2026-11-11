# expect: ?N is given twice
base(t:type) := class:
    F(?N:int=0,?M:int=0):int=N+M
ib := class(base(int)):
    Seed:int=3
    F<override>(?N:int=Seed,?M:int=N+1):int=N+M
Run(P:base(a) where a:type):int=P.F(?N:=1,?N:=2)
Main():void=Print("{Run(ib{})}")
