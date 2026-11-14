# expect: 4:0: the extension method Find on []int has the parameters of []int's own method Find
# An extension method does not repeat a method of its receiver's type, a
# built-in type's as a class's (Book of Verse ch. 6, 3532).
(A:[]int).Find(X:int):int = 7
Main():void =
    if (I := array{1, 2}.Find[2]) then Print("{I}")
