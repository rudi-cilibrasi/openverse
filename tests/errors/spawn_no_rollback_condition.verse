# expect: 10:13: this spawn has the 'no_rollback' effect, which a failure context does not allow
# A spawn in a failure context, an if's condition, is refused (#724): a
# spawn has the no_rollback effect, which UEFN 43.12 refuses in a <transacts>
# function (3512, followup-book2), as it refuses a call of a function without
# a heap specifier in a condition (followup/decides-plain-if).
Work()<suspends>:void =
    Print("spawned")
Main()<suspends>:void =
    Limit := 0
    if (T := spawn{Work()}, Limit > 0) then Print("condition succeeded")
