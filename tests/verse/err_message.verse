# Err(Message): the message is evaluated, then the program stops (Book of
# Verse ch. 8: "a runtime error with an optional message").
Message(S:string):string =
    Print("composing the message")
    "stopped: {S}"

Main():void =
    Print("before")
    Err(Message("here"))
