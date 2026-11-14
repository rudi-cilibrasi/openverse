# expect: 'public' is a reserved word: a value of the enum access_level takes it only qualified, (access_level:)public
# (Book of Verse ch. 9: "Qualification also allows you to use reserved words
# and keywords as enum values, which would otherwise cause errors";
# QualifiedIdentifier.versetest:315)
access_level := enum:
    Open
    public
Main():void = {}
