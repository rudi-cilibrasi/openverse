# expect: 7:26: this spawn has the 'no_rollback' effect, which a body whose effects exclude it does not allow
# A spawn has the no_rollback effect (#724): a <transacts> function cannot
# spawn. UEFN 43.12 (++Fortnite+Release-43.12-CL-60598086) refuses it with
# error 3512 (followup-book2/spawn-in-transacts-computes; the Book's
# Blueprint VM test Effects.versetest:557).
Work()<computes><suspends>:void = {}
Start()<transacts>:void = spawn{Work()}
Main()<suspends>:void =
    Start()
