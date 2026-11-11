# expect: expected int, found void
Main():void =
    for (V:int = if (true?) then (1 | 2)) { Print("{V}") }
