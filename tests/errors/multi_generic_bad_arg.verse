# expect: 5:14: expected []t, found int (in a call of Two)
# (#235, review of #282) an inlined generic call is checked against its parameters' types, as a plain generic call is
Two(A:[]t, B:t where t:type):t = B | B
Main():void =
    for (Z := Two(5, 6)) { Print("{Z}") }
