# An enum's value may take a reserved word's or an access specifier's name
# when it is qualified with its enum (Book of Verse ch. 9: "Qualification
# also allows you to use reserved words and keywords as enum values").
keyword_enum := enum:
    (keyword_enum:)public
    (keyword_enum:)decides
    Regular
Main():void =
    if (keyword_enum.Regular <> keyword_enum.public, keyword_enum.decides <> keyword_enum.public):
        Print("distinct")
