# expect: field 'Size' of big must have the type it inherits, int, or a type below it, not float
# "fields can only be overridden with subtypes" (Book of Verse ch. 10)
small := class:
    Size:int = 1
big := class(small):
    Size<override>:float = 2.0
Main():void = Print("ok")
