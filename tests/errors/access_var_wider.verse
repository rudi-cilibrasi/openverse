# expect: var<public> Level: setting it is more visible than reading it, <private> to gauge
# (Book of Verse ch. 12: "The write specifier must be at least as restrictive as the read specifier")
gauge := class:
    var<public> Level<private>:int = 0
Main():void = {}
