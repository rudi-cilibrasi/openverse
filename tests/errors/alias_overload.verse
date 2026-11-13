# expect: F is defined twice with parameters a call cannot tell apart, (int) and (int)
player_id := int
F(ID:player_id):void = {}
F(ID:int):void = {}
Main():void = {}
