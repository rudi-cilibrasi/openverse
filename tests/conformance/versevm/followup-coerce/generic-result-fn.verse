# followup-coerce (#724): Does UEFN 43.12 refuse a call of a generic
# function whose result has its type parameter inside a function type
# ((t->void)), at t = int (the shape of parametric-method-value's
# MakeClosure, without a class or a method)? OpenVerse's rule: refused,
# 3502. Control: generic-result-plain.
# OpenVerse refuses it: 3502 rule: using a value of type type{_(:t,
# :type{_(:t):void}):type{_(:t):void}} where t as a value of type
# type{_(:int, :type{_(:int):void}):type{_(:int):void}}
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19)
# refuses it: 3502 L13 "Using a value of type type{_(:t,:t->void where
# t):t->void} as a value of type tuple(int,type{_X:int where 1 <= _X, _X <=
# 5}->void)->(int->void) is not yet implemented."
TakeInt(X:int):void = Print("OVPROBE took {X}")
Wrap(X:t, F(:t):void where t:type):(t->void) = F

Main():void =
    G := Wrap(1, TakeInt)
    G(5)
