# expect: a case on the open enum dir needs _ (it may gain values)
dir := enum<open>:
    North
    South
Name(D:dir):string = case (D):
    dir.North => "n"
    dir.South => "s"
Main():void = Print(Name(dir.North))
