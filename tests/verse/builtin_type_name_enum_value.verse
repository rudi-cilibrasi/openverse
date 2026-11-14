# An enum's value, used qualified with its enum, may take a built-in type's
# name (Book of Verse ch. 9: qualification lets a value take any name).
kind := enum:
    int
    string
Main():void =
    K:kind = kind.string
    if (K = kind.string) then Print("string kind")
    if (K <> kind.int) then Print("not int")
