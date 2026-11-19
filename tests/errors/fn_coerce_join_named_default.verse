# expect: using a value of type type{_(?A:int = …):int} as a value of type type{_():int} is not yet implemented
# the branches of an if are F2 and F4, each with one named, defaulted
# parameter (?A, ?B), at type{_():int}: each needs a wrapper that gives its
# default, which Epic's Verse compiler does not make for a branch (UEFN 43.12,
# ++Fortnite+Release-43.12-CL-60598086, error 3502 at both branches:
# tests/conformance/versevm/followup-book2/join-named-default-fn; the Book of
# Verse's DefaultNamed.versetest 629, 640, bp_vm_only). F2 named alone at the
# type is admitted (fn_coerce_named_default_control).
F2(?A:int = 2):int = A
F4(?B:int = 4):int = B
Pick(Flag:logic):int =
    F:type{_():int} = if (Flag?) { F2 } else { F4 }
    F()
Main():void =
    Print("{Pick(true)} {Pick(false)}")
