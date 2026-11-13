# expect: 4:0: the receiver of an extension method is one parameter, (Name:type) or (:type): a tuple's type is written tuple(…) (Book of Verse ch. 6)
# The receiver of an extension method is one parameter (Book of Verse ch. 6:
# "You cannot use destructured parameter syntax")
(A:int, B:int).Method()<computes>:int = A + B
Main():void = {}
