# expect: 8:16: this call may signal an event (event.Signal), whose Signal has the no_rollback effect, in the block: of class loud
# (#515) a class's block: excludes no_rollback (Book of Verse tests,
# Effects.versetest:551; Epic's Verse compiler, UEFN 43.12: error 3512), so
# it cannot signal, also where no construction is in a failure context
loud := class:
    E:event(int)
    block:
        E.Signal(1)
Main():void =
    E := event(int){}
    if (L := loud{E := E}, 1 > 2) then Print("no") else Print("else")
