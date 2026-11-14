# expect: 4:19: a first generator needs an array, string or map, found int
# A first's generator takes what a for's does (Book of Verse ch. 7).
Main():void =
    if (X := first{V : 5; V > 0; V}) then Print("{X}")
