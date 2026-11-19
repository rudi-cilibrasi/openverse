# followup-coerce (#724): Does UEFN 43.12 admit an overloaded function named
# where one overload's function type is expected? The Book (ch. 6,
# "Capture") says an overloaded function cannot be captured; OpenVerse
# refuses it.
# OpenVerse refuses it: Over is overloaded: an overloaded function cannot be
# used as a value (Book of Verse ch. 6; Epic's Verse compiler, UEFN 43.12:
# error 3502, "Referencing an overloaded function without immediately
# calling it is not yet implemented", followup-coerce/overloaded-fn-value)
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19)
# refuses it: 3502 L11 "Referencing an overloaded function without
# immediately calling it is not yet implemented;
# (/invaliddomain/OVCompat:)Over or (/invaliddomain/OVCompat:)Over"
Over(X:int):int = X + 1
Over(X:string):int = 0

Main():void =
    F:type{_(:int):int} = Over
    Print("OVPROBE value {F(1)}")
