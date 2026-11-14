# The Book of Verse's weak-map examples (ch. 3, "Weak Maps", its blocks 69,
# 70, 74 and 76, as its tests run them: lines that are not type definitions
# are the body of a test), and the joins and meets of Tests/weak_map.versetest
# 98 and 113.

base_class := class<unique> {}
derived_class := class(base_class) {}
value_struct := struct {}

CreateDerivedMap():weak_map(derived_class, value_struct) = map{}

F(X:[int]int)<decides>:int = X[1]
G(X:weak_map(int, int))<decides>:int = X[3]

AttemptUpdate(GameData:weak_map(int, int))<transacts>:weak_map(int, int) =
    var Data:weak_map(int, int) = GameData
    if:
        set Data[1] = 100
        set Data[2] = 200
        false?
    Data

Main()<decides>:void =
    # block 69
    var MyWeakMap:weak_map(int, int) = map{}
    set MyWeakMap[0] = 1
    MyWeakMap[0] = 1
    set MyWeakMap = map{0 => 2}
    MyWeakMap[0] = 2
    # block 70
    var MyWeakMap2:weak_map(int, int) = map{1 => 2}
    MyWeakMap2[1] = 2
    # block 74: covariant in the key type
    BaseMap:weak_map(base_class, value_struct) = CreateDerivedMap()
    DerivedKey := derived_class{}
    RegularMap:[derived_class]value_struct = map{DerivedKey => value_struct{}}
    WeakMap:weak_map(base_class, value_struct) = RegularMap
    WeakMap[DerivedKey]
    not BaseMap[DerivedKey]
    # block 76: both updates rolled back
    GameData := AttemptUpdate(map{})
    not GameData[1]
    not GameData[2]
    # the join of a weak map and a map is a weak map (98)
    X:weak_map(int, int) = map{1 => 2, 3 => 4}
    J := if (true?) then X else map{5 => 6}
    J[1] = 2
    J[3] = 4
    # the meet of their parameters is the map (113)
    H := if (true?) then F else G
    H[map{1 => 2, 3 => 4}] = 2
    K := if (false?) then F else G
    K[map{1 => 2, 3 => 4}] = 4
    Print("ok")
