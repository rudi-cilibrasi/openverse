# expect: Items of pouch is <private>: only pouch's own code may use it
# (Book of Verse ch. 12, "Private"; Classes/AccessSpecifiers.versetest:62: error 3593)
pouch := class:
    Items<private>:[]int = array{1, 2}
    Count<public>():int = Items.Length
Peek(B:pouch):int = B.Items.Length
Main():void = Print("{Peek(pouch{})}")
