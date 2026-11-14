# expect: s is <persistable>, so its field 'Cache' must persist, and weak_map(int, int) does not
# Book of Verse ch. 17: "weak_map - Weak references are not persistable" (3662)
s := struct<persistable>:
    Cache:weak_map(int, int)
Main():void = {}
