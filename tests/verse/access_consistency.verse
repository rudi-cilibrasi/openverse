# A definition exposes nothing less visible than itself (Book of Verse ch. 11, 12;
# docs/research/access-specifiers.md): a <public> function in an internal module or class may
# name an internal class; a <private> method may; a field with a default or one as visible as
# the constructor; var<…> narrower than reading.
Shop<public> := module:
    ticket := class:
        N<public>:int = 1
    Desk := module:
        Issue<public>(N:int):ticket = ticket{N := N}     # Desk is internal to Shop
    counter<public> := class:
        Last<private>(T:ticket):int = T.N
        Sell<public>(N:int):int = Last(Desk.Issue(N))
    badge<public> := class<internal>:
        Code<internal>:int                               # the constructor is internal too
    Badge<public>():badge = badge{Code := 7}

    tally<public> := class:
        var<private> Count<public>:int = 0
        Bump<public>():int =
            set Count += 1
            Count
Main():void =
    Print("{Shop.counter{}.Sell(5)}")
    T := Shop.tally{}
    Print("{T.Bump()} {T.Bump()} {T.Count}")
