# Localize and Join in every place code is written (Book of Verse ch. 12,
# "Localization"): a struct's field's default as a class's, a block: clause,
# a parameter's default, a method's, a module's constant.
Hello<localizes>:message = "hello"
Greet<localizes>(Who:string):message = "hi {Who}"
Comma<localizes>:message = ", "
Bye<localizes>:message = "bye"
note := struct:
    Text:string = Localize(Hello)
    Both:string = Localize(Join(array{Hello, Bye}, Comma))
panel := class:
    Text:string = Localize(Bye)
    block:
        Print(Localize(Hello))
    Show(?Who:string = Localize(Greet("Cy"))):string = Who
Say(?What:string = Localize(Hello)):string = What
outer := module:
    inner<public> := module:
        Line<public>:string = Localize(Join(array{Hello, Hello}, Comma))
Main():void =
    N := note{}
    Print(N.Text)
    Print(N.Both)
    P := panel{}
    Print(P.Text)
    Print(P.Show())
    Print(Say())
    Print(outer.inner.Line)
