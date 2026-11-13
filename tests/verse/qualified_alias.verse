# A qualifier may name a class or an enum through a type alias, which stands
# for its type (docs/research/type-aliases.md): (box_alias:)V is box's V
box_alias := box
box := class:
    (box_alias:)V:int = 3
    Get():int = (box_alias:)V + Self.V
colour := enum{Red, Blue}
hue := colour
Main():void =
    Print("{box{}.Get()}")
    if ((hue:)Red <> (colour:)Blue) then Print("an alias qualifies a value too")
