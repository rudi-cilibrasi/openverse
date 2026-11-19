# followup-coerce2 (#724): Does UEFN 43.12 refuse an if whose branches
# return an int and a rational, at type{_():rational} (the Book's
# verse_vm_only Rational.versetest 127-140 join them; openverse's rule
# exempted int to rational)? OpenVerse admitted it until Epic answered.
# (Third returns 3, an int, as a rational.)
# OpenVerse refuses it: 3502 rule: using a value of type type{_():int} as a
# value of type type{_():rational}
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19)
# refuses it: 3502 L11 "Using a value of type tuple()->int as a value of
# type tuple()->rational is not yet implemented."
Three():int = 3
Third():rational = 3

Pick(Flag:logic):int =
    F:type{_():rational} = if (Flag?) { Three } else { Third }
    Floor(F())

Main():void =
    Print("OVPROBE true branch {Pick(true)}")
    Print("OVPROBE false branch {Pick(false)}")
