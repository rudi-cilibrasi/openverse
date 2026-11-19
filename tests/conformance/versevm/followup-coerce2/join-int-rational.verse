# followup-coerce2 (#724): Does UEFN 43.12 refuse an if whose branches
# return an int and a rational, at type{_():rational} (the Book's
# verse_vm_only Rational.versetest 127-140 join them; openverse's rule
# exempts int to rational)? OpenVerse admits it. (Third returns 3, an int,
# as a rational.)
# OpenVerse (Lean and C agreeing) prints true branch 3 | false branch 3
Three():int = 3
Third():rational = 3

Pick(Flag:logic):int =
    F:type{_():rational} = if (Flag?) { Three } else { Third }
    Floor(F())

Main():void =
    Print("OVPROBE true branch {Pick(true)}")
    Print("OVPROBE false branch {Pick(false)}")
