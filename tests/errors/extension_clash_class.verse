# expect: 6:0: the extension method Health on player has the parameters of player's method Health, (): a call could not tell them apart (Book of Verse ch. 6)
# An extension method cannot repeat a method of its receiver's class
# (Book of Verse ch. 6, error 3532)
player := class:
    Health():int = 100
(P:player).Health():int = 50
Main():void = {}
