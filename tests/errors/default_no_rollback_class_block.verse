# expect: 6:19: this invocation calls a function (F) that has the 'no_rollback' effect, which a body whose effects exclude it does not allow
# (#515, --default-no-rollback) nor can a class's block: (UEFN 43.12: error
# 3512; Book of Verse tests, Effects.versetest:551;
# tests/conformance/versevm/book/book-default-effect-in-class-block.verse)
F():void = {}
c := class {block{F()}}
Main():void =
    Print("compiled")
