# Book: Tests/Tuple.versetest:456 (bp_vm_only): the join of
# ArrayAndNamedToString(X:string, ?Y:int = 1) and ArrayToString(X:string) at
# type{_(:string):string} (written here with braces, not then/else). The
# Book's Blueprint VM refuses it in code generation (IR error 3502, twice);
# the Verse VM twin (:466-:474) is valid. OpenVerse prints
#   true branch hello | false branch hello
# If UEFN 43.12 refuses it (Build Verse Scripts, or the cook of a Verse VM
# session), Epic's shipped toolchain refuses a program OpenVerse runs.
# Control: join-named-tuple-control (one function, no join).
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 3502 (L13) "Using a value of type
# tuple([]char,?Y:int = ...)->[]char as a value of type []char->[]char is
# not yet implemented.".
ArrayAndNamedToString(X:string, ?Y:int = 1):string = X
ArrayToString(X:string):string = X

Pick(Flag:logic):string =
    F:type{_(:string):string} = if (Flag?) { ArrayAndNamedToString } else { ArrayToString }
    F("hello")

Main():void =
    Print("OVPROBE true branch {Pick(true)}")
    Print("OVPROBE false branch {Pick(false)}")
