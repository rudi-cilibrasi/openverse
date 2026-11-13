# expect: F is defined twice with parameters a call cannot tell apart, ([int]int) and (logic)
# false is the empty map and a logic (Book of Verse ch. 2): a call F(false)
# could be either
F(:[int]int):void = {}
F(:logic):void = {}
Main():void = {}
