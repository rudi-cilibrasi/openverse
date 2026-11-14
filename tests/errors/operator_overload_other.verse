# expect: operator'%': openverse takes overloads of the operators +, -, * and / and of prefix -
# (the Book of Verse's tests overload + - * / and prefix -, and refuse
# operator'()' with 3514; the comparison and mutation operators "aren't
# overloadable yet", Overloading.versetest:221-232)
num := struct{N:int}
operator'%'(L:num, R:num):num = L
Main():void = {}
