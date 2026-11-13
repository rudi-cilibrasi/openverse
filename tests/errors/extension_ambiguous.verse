# expect: 10:18: this call of Extra is ambiguous: b's own Extra and the extension method Extra both take it (Book of Verse ch. 6)
# A method of a class below the receiver's and an extension method that a
# call fits both: ambiguous (Book of Verse tests, error 3518)
c := class:
    Value:int = 1
(C:c).Extra(E:int):int = E + C.Value
b := class(c):
    Extra(E:int):int = E + 10 * Value
Main():void =
    X := b{}.Extra(100)
