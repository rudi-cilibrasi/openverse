# expect: 4:25: this for has several values, as its body has, and none when a body has none, so it can fail
# (#208) A for whose body has several values has none when a body has none, so a function whose
# value it is must be <decides>.
Rows()<computes>:[]int = for (X : array{1, 2}) { X | X + 10 }
Main():void =
    for (A := Rows()) { Print("{A.Length}") }
