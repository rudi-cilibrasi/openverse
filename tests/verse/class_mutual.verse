# Classes that require instances of each other (#37): their prototypes
# refer to each other, so variables of both types have initial values.
egg := class:
    var Hen:?hen = false
    Size:int = 1
hen := class:
    FirstEgg:egg
Lay(H:hen):egg = H.FirstEgg
Main():void =
    E := egg{}
    H := hen{FirstEgg := E}
    set E.Hen = option{H}
    var X:hen = H
    Print("{Lay(X).Size}")
