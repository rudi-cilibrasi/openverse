# expect: 5:9: this for has several values, as its body has, so it must be in a failure context that takes them
# (#208) A for whose body has several values has several values, which a failure context must
# take: a definition in a function's body is none.
Main():void =
    A := for (X : array{1, 2}) { X | X + 10 }
    Print("{A.Length}")
