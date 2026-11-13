# expect: expected int, found comparable
# nothing converts back from comparable (Book of Verse ch. 11 shows no
# conversion; ch. 17 calls it an abstract interface type)
Main():void =
    X:comparable = 1
    Y:int = X
