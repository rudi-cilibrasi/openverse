# expect: is a class (only <unique> classes are comparable, by identity)
# a class that is not <unique> is not comparable (Book of Verse ch. 11)
c := class{}
F(X:comparable):void = {}
Main():void = F(c{})
