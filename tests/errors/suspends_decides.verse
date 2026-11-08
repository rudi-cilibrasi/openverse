# expect: Get is both <suspends> and <decides>, which exclude each other
Get()<suspends><decides>:int = 1
Main():void = Print("x")
