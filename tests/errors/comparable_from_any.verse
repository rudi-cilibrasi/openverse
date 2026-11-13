# expect: expected comparable, found any
# any is not comparable (Book of Verse ch. 11, "You cannot use equality
# operators with any")
Main():void =
    X:any = 1
    Y:comparable = X
