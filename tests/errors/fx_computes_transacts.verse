# expect: Main has more than one of <converges>, <computes> and <transacts> (they exclude each other)
# <computes> and <transacts> are both exclusive (Book of Verse ch. 13)
Main()<computes><transacts>:void = Print("x")
