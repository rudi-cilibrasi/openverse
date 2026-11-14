# expect: 5:6: what follows a '.' must be on its line, with no comment between
# A comment between a '.' and its member is refused (Book of Verse tests, ReserveDotSpace.versetest:6).
c := class{F:int = 1}
Main():void =
    O.<# the field #>F = 1
