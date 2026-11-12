F(X:[string]int):string="map"
F(X:type{_(:string)<decides>:int}):string="function"
Main():void=Print(F(map{"a"=>1}))
