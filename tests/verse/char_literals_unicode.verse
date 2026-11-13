# A non-ASCII character in quotes is a char32 (Book of Verse ch. 1,
# "Character Literals": `Emoji := '😀'`, `Emoji = 0u1f600`), and a tab may be
# quoted as any character a string may hold (Book tests, Literals/Char).
Main():void =
    Emoji := '😀'
    Accented := 'é'
    Tab := '	'
    if (Emoji = 0u1f600, Accented = 0uE9, Tab = '\t'):
        Print("{Emoji}{Accented}|{Tab}|")
