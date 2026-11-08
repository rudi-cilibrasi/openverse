# generic code over an interface that declares fields, when every class
# implementing it fixes its type argument: the loop variable starts as a
# hidden placeholder laid out like the interface (#157)
slot(t:type) := interface:
    var Item:t
    Show():t
islot := class(slot(int)):
    A:int = 0
    Show<override>():int = Item + 1
sslot := class(slot(string)):
    Show<override>():string = Item
# a field at different places in its classes (`npre` lists a class first:
# read through accessors), and
# an interface below another, with a field of its own
named(t:type) := interface:
    Name:string
    var Val:t
    Get():t
nint := class(named(int)):
    Pad:int = 0
    Get<override>():int = Val * 2
nstr := class(named(string)):
    Get<override>():string = "{Name}:{Val}"
pre(t:type) := class:
    P:int = 0
npre := class(pre(int), named(int)):
    Get<override>():int = P + Val
tagged(t:type) := interface(named(t)):
    Tag:int
tint := class(tagged(int)):
    Get<override>():int = Val + Tag
Shows(Ss:[]slot(t) where t:type):[]t = for (S : Ss) { S.Show() }
Bumps(Ss:[]slot(t), X:t where t:type):void =
    for (S : Ss):
        set S.Item = X
Gets(Ns:[]named(t) where t:type):[]t = for (N : Ns) { N.Get() }
Names(Ns:[]named(t) where t:type):[]string = for (N : Ns) { N.Name }
Tags(Ts:[]tagged(t) where t:type):[]int = for (T : Ts) { T.Tag }
Main():void =
    I := islot{Item := 1}
    Bumps(array{I}, 41)
    for (X : Shows(array{I, islot{Item := 2}})) { Print("{X}") }
    for (X : Shows(array{sslot{Item := "a"}})) { Print(X) }
    for (X : Gets(array{nint{Name := "n", Val := 4}, npre{P := 10, Name := "p", Val := 5}})) { Print("{X}") }
    for (X : Names(array{npre{Name := "p", Val := 5}})) { Print(X) }
    for (X : Gets(array{nstr{Name := "s", Val := "v"}})) { Print(X) }
    for (X : Names(array{nstr{Name := "s", Val := "v"}, nstr{Name := "t", Val := "w"}})) { Print(X) }
    for (X : Tags(array{tint{Name := "t", Val := 1, Tag := 7}})) { Print("{X}") }
    for (X : Gets(array{tint{Name := "t", Val := 1, Tag := 7}})) { Print("{X}") }
