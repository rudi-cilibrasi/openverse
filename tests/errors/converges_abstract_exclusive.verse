# expect: more than one of <converges>, <computes> and <transacts>
# <converges> on a method without a body (#724) still excludes <computes>
# and <transacts> (Book of Verse ch. 13).
shape := class<abstract>:
    Area()<converges><computes>:int
Main():void = {}
