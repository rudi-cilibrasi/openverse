# Book: Tests/Intrinsics/ToDiagnostic.versetest:37 (verse_vm_only) prints 2^63
# as 9223372036854775808; docs/02_primitives.md says integers beyond 64 bits
# cannot be used in string interpolation.
Next(N:int)<computes>:int = N + 1

Main():void =
    Big := Next(9223372036854775807)
    Print("OVPROBE big computed")
    Print("OVPROBE value {Big}")
