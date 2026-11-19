# What a data member's definition (#724, Epic's 3582) may still do through
# the paths tests/errors/data_member_choice_* and data_member_nested_*
# refuse calls through: no call is written in these. A class's `block` is
# no data member: an archetype of a <computes> class whose block calls a
# function runs it (followup-3582/div-const-class-block asks UEFN 43.12); a
# constant that names a function as a value calls nothing
# (div-const-fn-value-call-control); a parametric class's archetype (the
# Book's tests, ParametricTypes.versetest:459-468); strings joined with `+`,
# an array's `+`; a `for` over literals with operators; and, in a function,
# a local constant that calls a function with several values
# (div-const-for-choice-call-control).
Next(X:int)<computes>:int = X + 1
Two(N:int)<computes>:int = N | N + 1
thing := class<computes>:
    Size:int = 3
    block:
        Next(Size)
box(t:type) := class<computes>:
    V:?t = false
Shared:thing = thing{}
Step:type{_(:int)<computes>:int} = Next
Empty:box(int) = box(int){}
Text:string = "a" + "b"
Squares:[]int = for (X : array{1, 2, 3}, X > 1) { X * X }
holder := class<computes>:
    Vals:[]int = for (X := 1..3) { X + 1 }
Main():void =
    Vals:[]int = for (X := Two(3)) { X }
    Print("size {Shared.Size} step {Step(1)} empty {if (Empty.V?) then 1 else 0}")
    Print("text {Text} squares {Squares.Length} vals {Vals.Length} holder {holder{}.Vals.Length}")
