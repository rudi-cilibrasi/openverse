# With --extended-defaults (#511, #724) a module's constant and a field's
# default may call a function of the program's, openverse's extension; a
# constant still writes nothing. UEFN 43.12 refuses both (3582,
# tests/conformance/versevm/followup-3582). So may they call a function
# with several values, in a `for`'s generator (refused without the option,
# tests/errors/data_member_choice_*).
Count()<computes>:int = 3
Two(N:int)<computes>:int = N | N + 1
thing := class<computes>:
    Size:int = Count()
    Pair:[]int = for (X := Two(1)) { X }
Limit:int = Count() + Min(1, 2)
Vals:[]int = for (X := Two(3)) { X }
Main():void = Print("{Limit} {thing{}.Size} {Vals.Length} {thing{}.Pair.Length}")
