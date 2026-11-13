# expect: struct1 is <persistable>, so its field 'X' must persist, and comparable does not
# comparable is not persistable (Book of Verse ch. 17, 178: "Abstract
# interface type")
struct1 := struct<persistable>:
    X:comparable
