# expect: (q:)X: X is a field of p, not of q
q := struct{X:int}
p := struct{(q:)X:int}
Main():void = {}
