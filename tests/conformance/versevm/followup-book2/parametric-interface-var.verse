# Book: Tests/ParametricFunctions.versetest:496 (untagged): a parametric
# interface with a var field of its parameter, i(t:type) := interface: var
# Data:t. The Book refuses it on both VMs, 3502. OpenVerse admits it and
# prints
#   defined
# Controls: parametric-interface-var-control (the field not var) and
# interface-var-field (a var field in an interface that is not parametric);
# if both are admitted and this is refused, the refusal is the
# combination's.
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 3502 (L10) "Mutable members in
# parametric interfaces are not yet implemented.".
i<public>(t:type) := interface:
    var Data<public>:t

Main():void =
    Print("OVPROBE defined")
