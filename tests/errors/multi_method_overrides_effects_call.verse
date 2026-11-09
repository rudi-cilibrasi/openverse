# expect: 7:43: Count calls shape.Sizes, which has the effect <writes>, which its effects (<computes>) do not allow: remove <computes>
# (a call has the effects the declaring class declares, whatever the receiver's type)
shape := class:
    Sizes()<transacts>:int = 1 | 2
big := class(shape):
    Sizes<override>()<computes>:int = 7 | 8
Count(B : big)<computes>:int = (for (X := B.Sizes()) { X }).Length
Main()<transacts>:void =
    Print("{Count(big{})}")
