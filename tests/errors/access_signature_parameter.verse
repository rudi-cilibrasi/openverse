# expect: the method Show of Shop.counter names Shop.ticket, which is less visible: Shop.ticket is internal to Shop
# (DigestVisibility.versetest:20: a public method of a public class names an internal class)
Shop<public> := module:
    ticket := class:
        N:int = 1
    counter<public> := class:
        Show<public>(T:ticket):int = T.N
Main():void = {}
