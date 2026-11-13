# expect: <allocates> on F is redundant: <transacts> implies it
F()<allocates><transacts>:void = {}
Main():void = F()
