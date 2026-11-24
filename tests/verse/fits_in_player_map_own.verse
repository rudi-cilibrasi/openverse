# FitsInPlayerMap is a soft built-in (#724): a program's own function of
# the name is the one it calls.
FitsInPlayerMap(X:int)<computes><decides>:int = X > 10
Main():void =
    if (not FitsInPlayerMap[5], Y := FitsInPlayerMap[50]) then Print("fits {Y}")
