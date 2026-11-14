# expect: construction of counter constructs an object that has a var field or is <unique>, which its effects (<computes>) do not allow
# <computes> alone allows no allocation (Book of Verse tests,
# Attributes/allocates.versetest:59, 3512)
counter := class<computes>:
    var N:int = 0
Main():void = Print("{counter{}.N}")
