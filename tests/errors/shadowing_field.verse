# expect: the field 'Limit' of box has the name of the constant Limit (2:0): Verse does not allow shadowing (Book of Verse ch. 10); rename one, or qualify this one, (box:)Limit
Limit:int = 3
box := class:
    Limit:int = 10
Main():void = {}
