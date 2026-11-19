# expect: 6:25: this spawn has the 'no_rollback' effect, which a body whose effects exclude it does not allow
# A <computes> function cannot spawn (#724): the Book's tests refuse it on
# both VMs with 3512 (Effects.versetest:558 and :573), as UEFN 43.12 refuses
# a spawn in any function with a heap specifier (followup-book2).
Work()<computes><suspends>:void = {}
Start()<computes>:void = spawn{Work()}
Main()<suspends>:void =
    Start()
