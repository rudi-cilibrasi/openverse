# expect: the method Hook of Shop.counter names Shop.ticket, which is less visible
# (DigestVisibility.versetest:27: a <protected> method reaches every class below, in any module)
Shop<public> := module:
    ticket := class:
        N:int = 1
    counter<public> := class:
        Hook<protected>(T:ticket):int = T.N
Main():void = {}
