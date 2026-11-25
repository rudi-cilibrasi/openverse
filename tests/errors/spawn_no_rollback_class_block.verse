# expect: 9:8: this spawn has the 'no_rollback' effect, which a body whose effects exclude it does not allow
# A class's block: excludes no_rollback (the Book's tests, Effects.versetest:551,
# refused by UEFN 43.12 with 3512), so it cannot spawn (#724: a spawn has
# no_rollback, followup-book2).
Work()<suspends>:void =
    Print("spawned")
holder := class:
    block:
        spawn{Work()}
Main()<suspends>:void =
    H := holder{}
