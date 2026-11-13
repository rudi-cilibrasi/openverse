# expect: 4:0: F is defined twice with parameters a call cannot tell apart, (int) and (void)
# The Book's example (ch. 6): void accepts any value, so these overlap.
F(:int):void = {}
F(:void):void = {}
Main():void = {}
