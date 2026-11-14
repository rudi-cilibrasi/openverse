# expect: expected weak_map(class2, int), found weak_map(class1, int)
# covariant in the key, not the other way (weak_map.versetest:55, 3509)
class1 := class<unique> {}
class2 := class(class1) {}
F(Data:weak_map(class1, int)):void =
    OtherData:weak_map(class2, int) = Data
Main():void = {}
