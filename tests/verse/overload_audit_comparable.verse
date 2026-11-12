Choose(X:t, Y:t where t:subtype(comparable))<computes>:t = X
Choose(?Label:string)<computes>:string = Label
Main():void =
    Print("{Choose(3, 4)} {Choose(?Label:="word")}")
