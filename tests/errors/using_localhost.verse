# expect: 4:0: using{/localhost/something}: /localhost is the package the program is in
# A using does not name /localhost (Book of Verse tests, Modules/Using2.versetest:
# "Explicitly using something in a "/localhost" package is not allowed").
using{/localhost/something}
Main():void = {}
