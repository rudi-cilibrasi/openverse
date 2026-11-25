# Book: Tests/Features/DefaultValueAssignment.versetest:289 (verse_vm_only,
# assert_valid): two classes whose field defaults construct each other.
# Nothing constructs them.
c41 := class{M:c42 = c42{}}
c42 := class{M:c41 = c41{}}

Main():void =
    Print("OVPROBE compiled")
