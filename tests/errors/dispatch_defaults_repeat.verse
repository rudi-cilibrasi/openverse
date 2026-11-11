# expect: branch cannot be in a loop or for body
base(t:type) := class:
    Go(?N:int=0)<suspends>:void=Print("{N}")
ib := class(base(int)):
    Seed:int=3
    Go<override>(?N:int=block{ branch{Sleep(0.1);Print("later")};Seed })<suspends>:void=Print("{N}")
Run(P:base(a) where a:type)<suspends>:void=
    for(I:=1..2):P.Go()
Main()<suspends>:void=Run(ib{})
