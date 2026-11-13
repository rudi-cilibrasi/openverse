# expect: F is defined twice with parameters a call cannot tell apart, (int) and (comparable)
# every int is a comparable (Book of Verse ch. 11, "int is already
# comparable"): F(1) could be either
F(:int):void = {}
F(:comparable):void = {}
Main():void = {}
