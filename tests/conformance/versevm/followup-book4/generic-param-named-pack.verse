# Edge of the 3509 rule (#724), rewritten: F(1, 2, ?E := 5) of
# F(X:t, ?E:int where t:type), several arguments for a generic parameter
# beside a named one. The first version, F(X:t, ?E:int = 0 where t:type),
# was refused for its form, not this question: UEFN 43.12 read the default
# as `0 where t:type` (3502 "The 'where' operator is limited to numeric
# range-like clauses with literal bounds", 3506 "Unknown identifier `t`").
# This one has no default before `where`; if Epic reads `int where t:type`
# as a refinement and refuses it the same way, the question stays open.
# Epic refuses several arguments for a tuple and an array parameter beside
# a named one (followup-book2/overload-tuple-named-call,
# followup-book3/array-named-pack). OpenVerse still packs them into t's
# tuple and prints
#   result 5
# If Epic refuses it (3509), a generic parameter beside a named one takes
# no several arguments either. Epic's compiler (UEFN 43.12,
# ++Fortnite+Release-43.12-CL-60598086, BuildAll, 2026-11-19 ~20:40Z)
# refuses it: 3509 (L18) "This function parameter expects a value of type
# tuple(any,?E:int), but this argument is an incompatible value of type
# tuple(type{1},type{2},?E:type{5})". OpenVerse refuses it now.
F(X:t, ?E:int where t:type):int = E

Main():void =
    Print("OVPROBE result {F(1, 2, ?E := 5)}")
