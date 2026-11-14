# expect: expected [class1]int, found weak_map(class2, int): a weak_map is no map
# weak_map.versetest:62, 3509
class1 := class<unique> {}
class2 := class(class1) {}
F(Data:weak_map(class2, int)):void =
    OtherData:[class1]int = Data
Main():void = {}
