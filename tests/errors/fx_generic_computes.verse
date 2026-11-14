# expect: Id sets a var field, which its effects (<reads>) do not allow
c := class{var N:int = 0}
Id(X:t, C:c where t:type)<computes><reads>:t =
    set C.N = C.N + 1
    X
Main():void = Print("{Id(1, c{})}")
