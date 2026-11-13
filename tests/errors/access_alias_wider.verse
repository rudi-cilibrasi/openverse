# expect: the type alias handle names widget, which is less visible: widget is internal to the top level
# (Book of Verse ch. 11: "A type alias cannot be more public than the type it aliases"; TypeAlias.versetest:228)
widget := class:
    N:int = 1
handle<public> := widget
Main():void = {}
