# `any` and `comparable` are types, so values of `type` (Book of Verse
# ch. 11, "Metatypes"; the tests pass them where a type is,
# GetCastableFinalSuperClass.versetest 302, 304)
Types():[]type = array{any, comparable, int}
Main():void =
    X:type = any
    Print("{Types().Length}")
