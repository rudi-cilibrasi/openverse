# expect: 8:26: expected type{_()<decides><transacts>:int}, found type{_():int}
# (#515, --default-no-rollback) and a function without specifiers is no
# value of a function type without no_rollback: UEFN 43.12 refuses this
# with error 3509 (Book of Verse tests, FunctionTypes.versetest:191;
# tests/conformance/versevm/book/book-function-subtype-decides.verse)
f19():int = return 1
f24(g()<transacts><decides>:int):int = 3
Main():void = Print("{f24(f19)}")
