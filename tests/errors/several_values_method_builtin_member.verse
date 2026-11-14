# expect: 6:4: c.ReplaceFirstElement has several values, but ReplaceFirstElement is also the name of
# A method with several values is inlined before types are known, so it
# takes no name of a built-in type's member, as A.ReplaceFirstElement[…] of
# an array could be its call: refused, as Last is.
c := class:
    ReplaceFirstElement(X:int, Y:int):int = X | Y
Main():void =
    for (V := c{}.ReplaceFirstElement(1, 2)) { Print("{V}") }
    if (B := array{1, 2}.ReplaceFirstElement[1, 5]) then Print("{B.Length}")
