# expect: using{/localhostkinda}: the path names no package
# (Book of Verse ch. 16: "all imports must be resolvable when your code is
# compiled"; its tests, Modules/Using2.versetest:94, 3587)
using{/localhostkinda}
Main():void = {}
