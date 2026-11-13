# expect: 4:23: tuple(int, char) has no method 'Slice'
# A tuple of elements of different types is no array.
Main()<decides>:void =
    S := (1, 'a').Slice[0]
