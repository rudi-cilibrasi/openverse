# expect: 9:14: this call may signal an event (Note → event.Signal), whose Signal has the no_rollback effect, in the block: of class loud
# (#515) a class's block: excludes no_rollback, so it cannot signal, even
# through a function, and even where no construction is in a failure
# context (UEFN 43.12 refuses a block calling a function without specifiers
# with error 3512: tests/conformance/versevm/book/book-default-effect-in-class-block.verse)
Note(E:event(int)):void = E.Signal(1)
loud := class:
    E:event(int)
    block{Note(E)}
Main():void =
    L := loud{E := event(int){}}
    Print("built")
