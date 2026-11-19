# With --extended-defaults (#511, #724) a module's constant and a field's
# default may call a function of the program's, openverse's extension; a
# constant still writes nothing. UEFN 43.12 refuses both (3582,
# tests/conformance/versevm/followup-3582).
Count()<computes>:int = 3
thing := class<computes>:
    Size:int = Count()
Limit:int = Count() + Min(1, 2)
Main():void = Print("{Limit} {thing{}.Size}")
