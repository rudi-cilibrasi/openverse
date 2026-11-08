# overrides in classes that fix a type argument to an array or an option,
# called from code generic over all or part of it (#142)
box(t:type) := class:
    V:t
    Describe():string = "box"
arr_box := class(box([]int)):
    Describe<override>():string = "arr_box {V.Length}"
opt_box := class(box(?string)):
    Describe<override>():string = if (X := V?) then "opt_box {X}" else "opt_box none"
DescribeAny(B:box(t) where t:type):string = B.Describe()
DescribeArr(B:box([]u) where u:type):string = B.Describe()
Main():void =
    Print(DescribeAny(arr_box{V := array{1, 2, 3}}))
    Print(DescribeAny(opt_box{V := option{"x"}}))
    Print(DescribeAny(opt_box{V := false}))
    Print(DescribeAny(box(int){V := 1}))
    Print(DescribeArr(arr_box{V := array{4}}))
    Print(DescribeArr(box([]string){V := array{"a"}}))
