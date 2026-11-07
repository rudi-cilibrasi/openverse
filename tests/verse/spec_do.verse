# openverse run FILE do EXPR (#25): EXPR runs instead of Main, in the context
# of the file's definitions, and its value is printed (see spec_do.args).
Twice(X:int):int = X * 2
Greeting:string = "hello"
Main():void = Print("Main does not run")
