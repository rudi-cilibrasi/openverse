# open enums (Book of Verse ch. 9): enum<open> may gain values, so a case on
# one needs _ or a failure context; enum<closed> is the default

dir := enum<open>:
    North
    South
mode := enum<closed>{On, Off}
Name(D:dir):string = case (D):
    dir.North => "n"
    dir.South => "s"
    _ => "?"
Try(D:dir)<decides>:string = case (D):
    dir.North => "n"
    dir.South => "s"
M(X:mode):int = case (X):
    mode.On => 1
    mode.Off => 0
Main():void =
    Print("{Name(dir.North)} {Name(dir.South)} {M(mode.On)}")
    if (T := Try[dir.South]) then Print(T)
