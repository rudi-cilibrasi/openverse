# expect: parameters a call cannot tell apart
Choose(X:t, Y:t where t:subtype(comparable))<computes>:t = X
Choose(X:string)<computes>:string = X
Main():void =
    Print("{Choose(3, 4)} {Choose("word")}")
