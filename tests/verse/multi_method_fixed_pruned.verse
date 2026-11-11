box(t:type) := class:
    A:t
    Both():t = A | A
fixed := class(box(int)):
    Both<override>():int = A + 1 | A + 2
Main():void =
    for (V := box(string){A:="s"}.Both()) { Print("{V}") }
