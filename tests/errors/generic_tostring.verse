# expect: no ToString for t
Show(X:t where t:type):string = "{X}"

Main():void = Print(Show(1))
