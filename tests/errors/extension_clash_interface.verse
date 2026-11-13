# expect: 5:0: the extension method Scale on i has the parameters of i's method Scale, (int): a call could not tell them apart (Book of Verse ch. 6)
# ... nor an interface's, with parameters
i := interface:
    Scale(E:int):int
(I:i).Scale(E:int):int = E
Main():void = {}
