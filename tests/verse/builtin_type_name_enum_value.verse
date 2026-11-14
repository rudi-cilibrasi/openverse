# An enum's value may take a built-in type's name written qualified with
# its enum, as a reserved word may (Book of Verse ch. 9, "Explicit
# Qualification"), and is used qualified.
kind := enum:
    (kind:)int
    (kind:)string
    other
Main():void =
    K:kind = kind.string
    if (K = kind.string) then Print("string kind")
    if (K <> kind.int) then Print("not int")
