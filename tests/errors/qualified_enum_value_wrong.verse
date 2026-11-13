# expect: (f:)A: A is a value of e, not of f
f := enum{A}
e := enum{(f:)A, B}
Main():void = {}
