# expect: F takes 1 positional argument(s), found 2: several arguments do not make an array parameter beside a named one
# Two arguments do not make an array parameter beside a named one (#724):
# UEFN 43.12 (++Fortnite+Release-43.12-CL-60598086) refuses F(1, 2) of
# F(A:[]int, ?B:int = 2), error 3509, "This function parameter expects a
# value of type tuple([]int,?B:int = ...), but this argument is an
# incompatible value of type tuple(type{1},type{2})"
# (followup-book3/array-named-pack).
F(A:[]int, ?B:int = 2):int = A.Length + B
Main():void = Print("{F(1, 2)}")
