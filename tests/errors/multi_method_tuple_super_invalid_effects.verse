# expect: mid.Pick allows the effect <allocates>, which base.Pick, which it overrides, does not
base(t:type) := class:
    Pick(X:t,Y:t)<computes>:int = 1 | 2
mid(u:type) := class(base(u)):
    Pick<override>(X:u,Y:u)<transacts>:int =
        Print("wrong")
        (super:)Pick((X,Y))
Main()<transacts>:void = for(N:=mid(int){}.Pick(1,2)){Print("{N}")}