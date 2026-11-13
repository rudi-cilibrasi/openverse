# expect: 6:0: the extension method Name on derived has the parameters of the method Name derived inherits from base, (): a call could not tell them apart (Book of Verse ch. 6)
# ... nor one the class inherits
base := class:
    Name():string = "base"
derived := class(base){}
(D:derived).Name():string = "derived"
Main():void = {}
