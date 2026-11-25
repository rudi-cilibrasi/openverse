# expect: FitsInPlayerMap takes a value of a persistable type
# FitsInPlayerMap(Value:t where t:subtype(persistable)) (#724): a class
# does not persist.
c := class:
    X:int = 0
Main():void =
    if (Y := FitsInPlayerMap[c{}]) then Print("fits")
