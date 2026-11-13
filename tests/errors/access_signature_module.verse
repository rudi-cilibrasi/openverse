# expect: Shop.Show names Shop.Inner.ticket, which is less visible: Shop.Inner.ticket is in Shop.Inner, which is internal to Shop
# (the restriction is the module's: DigestVisibility.versetest:33-54)
Shop<public> := module:
    Inner := module:
        ticket<public> := class{}
    Show<public>(T:Inner.ticket):int = 1
Main():void = {}
