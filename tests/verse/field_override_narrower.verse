# A field that is no var re-declared at a type below the one it inherits
# (Book of Verse ch. 10, "Overriding Members": "Field overrides can provide
# different default values or specialize to subtypes"): read through the
# class that narrows it, the narrower type; through a class or interface
# above, the inherited one.
animal := class:
    Name:string = "animal"
cat := class(animal):
    Name<override>:string = "cat"
    Purr():string = "purr"
shelter := class:
    Pet:animal = animal{}
    Kind:comparable = 0
    Tag:any = false
    Show():string = "{Pet.Name}"
cattery := class(shelter):
    Pet<override>:cat = cat{}
    Kind<override>:int = 7
    Tag<override>:int = 3
small_cattery := class(cattery):
    Kind<override>:int = 2
percent := type{X:int where 0 <= X, X <= 100}
gauge := interface:
    Level:int
    Pair:[]int
meter := class(gauge):
    Level<override>:percent = 40
    Pair<override>:tuple(int, int) = (1, 2)
Describe(S:shelter):string = if (S.Kind = 7) then "seven" else "other"
Main():void =
    C := cattery{}
    S:shelter = C
    Print("{C.Pet.Purr()} {S.Pet.Name} {S.Show()} {C.Kind + 1} {C.Tag + 1} {Describe(S)} {Describe(shelter{})}")
    Small:shelter = small_cattery{}
    Print("{Describe(Small)} {small_cattery{}.Kind}")
    M := meter{}
    G:gauge = M
    var Levels:[percent]int = map{}
    if (set Levels[M.Level] = 1) {}
    Print("{G.Level} {M.Pair(1)} {G.Pair.Length} {Levels.Length}")
