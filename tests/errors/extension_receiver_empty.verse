# expect: 3:0: the receiver of an extension method is one parameter, (Name:type) or (:type): a tuple's type is written tuple(…) (Book of Verse ch. 6)
# `().M()` is not an extension method: its receiver is one parameter
().Magic():int = 0
Main():void = {}
