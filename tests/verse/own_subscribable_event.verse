# a program's own class named subscribable_event: no prelude, and its own
# type arguments, void too
subscribable_event(t:type) := class:
    Count:int = 0
Main():void =
    E := subscribable_event(void){Count := 3}
    Print("{E.Count}")
