# expect: field 'Value' of interface I1 is a field of an interface above it
# An interface declares no inherited field again (the Book's tests,
# InterfaceWithFields.versetest, 3532)
I0 := interface {Value:int}
I1 := interface(I0) {Value:int}
Main():void = {}
