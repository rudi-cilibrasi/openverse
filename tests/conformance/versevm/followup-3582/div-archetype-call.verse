# 3582 follow-up (#724): a field given by a call in the archetype at the
# instantiation site, inside a function. Control: not a data-member
# definition.
Count():int = 3

thing := class:
    Size:int = 0

Main():void =
    T := thing{Size := Count()}
    Print("OVPROBE size {T.Size}")
