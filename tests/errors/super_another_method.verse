# expect: (super:)Other is not in an override of Other
# (super:)M calls the implementation above of the method it is in: not of
# another method (the Book's tests, Super.versetest: "super on another
# method"), nor of one nothing above has ("super on method not in super
# class")
base := class {}
child := class(base):
    Other():int=7
    Values():int=(super:)Other()|9
Main():void=for(V:=child{}.Values()):Print("{V}")
