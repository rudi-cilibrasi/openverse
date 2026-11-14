# expect: expected class2, found class3
# a key of a sibling class does not write (Map.versetest:410, 3509)
class1 := class<unique> {}
class2 := class(class1) {}
class3 := class(class1) {}
Main()<decides>:void =
    var X:weak_map(class2, int) = map{}
    set X[class3{}] = 1
