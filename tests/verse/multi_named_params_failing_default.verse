# A function with several values whose omitted default fails, inlined (#283):
# the call of a <decides> one fails. openverse's reading of a default
# (--extended-defaults); the Book refuses a default that can fail
# (DefaultNamed.versetest:820), which multi_named_params follows.
Arr : []int = array{1, 2}
Dec(A : int, ?B : int = Arr[A])<decides><transacts>:int = A | B
Main()<transacts>:void =
    for (X := Dec[1]):
        Print("dec {X}")
    for (X := Dec[5]):
        Print("never {X}")
