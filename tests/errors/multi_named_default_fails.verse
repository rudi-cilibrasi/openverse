# expect: 3:25: the default of ?B of F can fail: a default is no failure context, also of a <decides> function
Arr : []int = array{1}
F(A : int, ?B : int = Arr[5])<transacts>:int = A | B
Main()<transacts>:void =
    for (X := F(1)):
        Print("{X}")
