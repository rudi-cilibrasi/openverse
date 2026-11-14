# expect: _X > 9223372036854775807 admits no int
t := type{_X:int where _X > 9223372036854775807}
Main():void = {}
