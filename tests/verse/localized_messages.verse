# Localized messages (Book of Verse ch. 12, "Localization"; its tests,
# Localization.versetest, LocalizationJoin.versetest): a <localizes>
# definition of type message is its default text, rendered by Localize: an
# int with comma separators, a name that is no parameter as written, a code
# point as its character; Join puts a separator between messages.
Welcome<localizes>:message = "Welcome to the game!"
Score<localizes>(Player:string, Points:int):message = "{Player} has {Points} points, {Player}!"
Spaced<localizes>(Name:string):message = "Hello { Name } from {Elsewhere} and {0u004d}"
Config<localizes>(?Players:int = 8, ?Limit:int = 300):message = "{Players} players, {Limit} s"
Location<localizes>(Who:string, (X:int, Y:int)):message = "{Who} is at ({X}, {Y})"
Comma<localizes>:message = ", "
panel := class:
    Title<localizes>:message = "Base"
fancy_panel := class(panel):
    Title<localizes><override>:message = "Fancy"
Main():void =
    Print(Localize(Welcome))
    Print(Localize(Score("Ana", 1234567)))
    Print(Localize(Score("Bo", -1005)))
    Print(Localize(Spaced("Cy")))
    Print(Localize(Config(?Limit := 60)))
    Print(Localize(Location("Di", (10, 20))))
    Print(Localize(Join(array{Welcome, Spaced("Ed"), Comma}, Comma)))
    Print(Localize(Join(array{}, Comma)))
    P:panel = fancy_panel{}
    Print(Localize(P.Title))
    Print(Localize(12345))
