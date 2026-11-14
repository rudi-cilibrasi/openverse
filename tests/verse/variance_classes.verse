# Variance of parametric classes (Book of Verse ch. 10, "Instantiation and
# Identity"): a type parameter used only where values come out (fields that
# are no `var`, results) is covariant, only where they go in (parameters)
# contravariant, nowhere bivariant; through a subclass and its overrides.
entity := class:
    ID:int
player := class(entity):
    Name:string
producer(t:type) := class:
    Value:t
    Get():t = Value
named(t:type) := class(producer(t)):
    Label:string
    Get<override>():t = Value
consumer(t:type) := class:
    Process(Item:t):int = 1
counter(t:type) := class(consumer(t)):
    Process<override>(Item:t):int = 2
container(t:type) := class:
    Size():int = 3
ProcessProducer(P:producer(entity)):int = P.Get().ID
ProcessPlayers(C:consumer(player)):int = C.Process(player{ID := 9, Name := "Bob"})
Main():void =
    PlayerProducer:producer(player) = producer(player){Value := player{ID := 1, Name := "Alice"}}
    EntityProducer:producer(entity) = PlayerProducer
    Print("covariant {ProcessProducer(PlayerProducer)} {EntityProducer.Value.ID} {EntityProducer.Get().ID}")
    N:producer(entity) = named(player){Value := player{ID := 2, Name := "Ann"}, Label := "n"}
    Print("override {N.Get().ID} {ProcessProducer(named(player){Value := player{ID := 3, Name := "C"}, Label := ""})}")
    NN:named(entity) = named(player){Value := player{ID := 4, Name := "D"}, Label := "m"}
    Print("subclass {NN.Get().ID} {NN.Label}")
    EntityConsumer:consumer(entity) = consumer(entity){}
    PlayerConsumer:consumer(player) = EntityConsumer
    Print("contravariant {ProcessPlayers(EntityConsumer)} {PlayerConsumer.Process(player{ID := 5, Name := "E"})}")
    CC:consumer(player) = counter(entity){}
    Print("contravariant override {CC.Process(player{ID := 6, Name := "F"})}")
    X:container(entity) = container(player){}
    Y:container(player) = X
    Z:container(int) = container(string){}
    Print("bivariant {X.Size()} {Y.Size()} {Z.Size()}")
