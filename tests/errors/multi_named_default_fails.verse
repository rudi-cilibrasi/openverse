# expect: 5:14: the default of ?B of F can fail, but F is not <decides>
Arr : []int = array{1}
F(A : int, ?B : int = Arr[5])<transacts>:int = A | B
Main()<transacts>:void =
    for (X := F(1)):
        Print("{X}")
