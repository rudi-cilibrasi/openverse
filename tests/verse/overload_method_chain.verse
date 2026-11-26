# A chain of calls of an overloaded method, each on the result of the call
# before it (#771). A call of an overloaded method elaborated its receiver
# once to find the overloads and once more in the call of the overload it
# fits, so each call of a chain doubled the time to compile it: sixteen calls
# took ten seconds, and the forty of the first chain here would not end. The
# receiver is elaborated once now, and the chain takes time in proportion to
# its length.
# Each call appends what says which overload took it: `s` for the string's,
# `c` for the char's, the number for the int's; `.` is the method that is
# not overloaded and `g` the overloaded function. So a chain prints its calls
# in the order they are made, each receiver before its call's argument.
trail := class:
    T:string = ""
    M(S:string):trail = trail{T := "{T}s"}
    M(K:char):trail = trail{T := "{T}c"}
    M(N:int):trail = trail{T := "{T}{N}"}
    P():trail = trail{T := "{T}."}
    # (fails once the trail is as long as `Most`)
    F(S:string, Most:int)<decides><transacts>:trail =
        T.Length < Most
        trail{T := "{T}s"}
    F(N:int, Most:int)<decides><transacts>:trail =
        T.Length < Most
        trail{T := "{T}{N}"}
    Run():string = Self.M(1).M("a").M('b').M(2).M("a").M('b').M(3).M("a").M('b').M(4).M("a").M('b').T
holder := class:
    Inner:trail
    H(S:string):holder = holder{Inner := Inner.M(S).P()}
    H(N:int):holder = holder{Inner := Inner.M(N)}
box(t:type) := class:
    V:t
    T:string = ""
    Add(S:string):box(t) = box(t){V := V, T := "{T}s"}
    Add(N:int):box(t) = box(t){V := V, T := "{T}{N}"}
walk := interface:
    Step(S:string):walk
    Step(N:int):walk
    Said():string
walker := class(walk):
    T:string = ""
    Step<override>(S:string):walk = walker{T := "{T}s"}
    Step<override>(N:int):walk = walker{T := "{T}{N}"}
    Said<override>():string = T
G(V:trail):trail = trail{T := "{V.T}g"}
G(S:string):trail = trail{T := "G"}
D(V:trail):string = "trail {V.T}"
D(S:string):string = "string {S}"
Log(S:string):string =
    Print("arg {S}")
    S
Main():void =
    X := trail{}
    # forty calls: the same ten four times
    Print(X.M("a").M('b').M(1).M("a").M("a").M('b').M('b').M(2).M(3).M("a").M("a").M('b').M(1).M("a").M("a").M('b').M('b').M(2).M(3).M("a").M("a").M('b').M(1).M("a").M("a").M('b').M('b').M(2).M(3).M("a").M("a").M('b').M(1).M("a").M("a").M('b').M('b').M(2).M(3).M("a").T)
    # among calls of a method that is not overloaded
    Print(X.M("a").P().M('b').P().P().M(5).M("a").P().M('b').P().P().M(5).M("a").P().M('b').P().P().M(5).T)
    # through a field
    Y := holder{Inner := trail{}}
    Print(Y.H("a").H(1).Inner.M('b').M(2).M("a").M('b').M(3).M("a").M('b').M(4).M("a").M('b').M(5).M("a").T)
    Print(Y.H("a").H(1).H("a").H(2).H("a").H(3).H("a").H(4).H("a").H(5).H("a").H(6).H("a").H(7).H("a").H(8).Inner.T)
    # on the result of an overloaded function, itself taking such a chain
    Print(G(G(G(G(G(G("x").M(1)).M("a")).M('b')).M(2)).M("a")).M('b').M(3).M("a").M('b').M(4).M("a").M('b').T)
    # the chain as the argument of an overloaded call
    Print(D(X.M("a").M('b').M(1).M("a").M("a").M('b').M('b').M(2).M(3).M("a").M("a").M('b').M(1).M("a").M("a").M('b').M('b').M(2).M(3).M("a")))
    # calls that can fail, in a failure context: all succeed, then the ninth fails
    if (Z := X.F["a", 99].F[1, 99].F["a", 99].F[2, 99].F["a", 99].F[3, 99].F["a", 99].F[4, 99].F["a", 99].F[5, 99].F["a", 99].F[6, 99]):
        Print(Z.T)
    else:
        Print("failed")
    if (Z := X.F["a", 8].F[1, 8].F["a", 8].F[2, 8].F["a", 8].F[3, 8].F["a", 8].F[4, 8].F["a", 8].F[5, 8].F["a", 8].F[6, 8]):
        Print(Z.T)
    else:
        Print("failed after eight")
    # a generic class's
    B := box(int){V := 41}.Add("a").Add(1).Add(2).Add("a").Add(3).Add(4).Add("a").Add(5).Add(6).Add("a").Add(7).Add(8)
    Print("{B.T} {B.V}")
    # an interface's
    W:walk = walker{}
    Print(W.Step("a").Step(1).Step("a").Step(2).Step("a").Step(3).Step("a").Step(4).Step("a").Step(5).Step("a").Step(6).Said())
    # in a method, on Self
    Print(X.Run())
    # each receiver is evaluated once, before its call's argument
    Print(X.M(Log("one")).M(Log("two")).M(Log("three")).M(Log("four")).M(Log("five")).M(Log("six")).M(Log("seven")).M(Log("eight")).M(Log("nine")).M(Log("ten")).M(Log("eleven")).M(Log("twelve")).T)
