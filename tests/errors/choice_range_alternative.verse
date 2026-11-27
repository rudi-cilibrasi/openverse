# expect: 5:20: a range a..b can only be the source of a for clause
# (#208) A range is no alternative of a choice: the Book of Verse, ch. 1, "Ranges are not
# first-class values. They cannot be stored in variables or used outside of `for` loop iteration clauses".
Main():void =
    for (X := 7 | (1..2)) { Print("{X}") }
