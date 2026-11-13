# A tuple of one element type is an array of its elements where an array is
# expected, also as the receiver of an array method (the Book's tests:
# ('a','b','c','d','e','f').Slice[0, 5]).
Main():void =
    if (S := ('a', 'b', 'c', 'd', 'e', 'f').Slice[1, 4], I := (10, 20, 30).Find[20]):
        Print("{S} {I}")
