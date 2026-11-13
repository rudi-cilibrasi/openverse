# expect: the branches have different types: incomparable_class and int
# the join of a class that is not <unique> and an int is not comparable
# comparable (Book of Verse Tests/Comparable.versetest 200 to 203)
incomparable_class := class{}
F(:comparable):void = {}
G(X:?incomparable_class):void = F(X? or 1)
Main():void = {}
