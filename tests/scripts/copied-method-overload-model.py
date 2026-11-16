#!/usr/bin/env python3
"""Copied method-list programs, typed controls and complete value/effect oracles."""

def cases():
    specs = []
    dup = 'Dup(V:t where t:type)<transacts>:t=V|V\n'
    basic = 'a:=class:\n    M(N:int)<transacts>:int=N|N+1\n    M(S:string)<transacts>:int=7|8\n'
    override = basic + 'b:=class(a):\n    M<override>(N:int)<transacts>:int=N+10|N+11\n    M<override>(S:string)<transacts>:int=17|18\n'
    generic_class = 'box(t:type):=class:\n    Value:t\n    M(N:int)<transacts>:t=Value|Value\n    M(S:string)<transacts>:t=Value|Value\n'
    generic_method = 'a:=class:\n    M(N:int,V:t where t:type)<transacts>:t=V|V\n    M(S:string,V:t where t:type)<transacts>:t=V|V\n'
    for name, decl, call, values, threshold in [('basic', basic, 'a{}.M(X)', ['1', '2', '1', '2', '7', '8', '7', '8'], 6), ('override', override, 'b{}.M(X)', ['11', '12', '11', '12', '17', '18', '17', '18'], 16), ('generic-class', generic_class, 'box(string){Value:="v"}.M(X)', ['v'] * 8, None), ('generic-method', generic_method, 'a{}.M(X,"v")', ['v'] * 8, None)]:
        prefix = decl + dup + 'Main()<transacts>:void=\n'
        direct = prefix + f'    for(X:=(Dup(1)|Dup("s")),Y:={call}){{Print("y {{Y}}")}}\n'
        control = prefix + f'    for(X:=Dup(1),Y:={call}){{Print("y {{Y}}")}}\n' + f'    for(X:=Dup("s"),Y:={call}){{Print("y {{Y}}")}}\n'
        specs.append((name + '-for', direct, control, ''.join(('y ' + v + '\n' for v in values))))
        if threshold is not None:
            literal = '|'.join(values)
            condition = f'Y>{threshold}'
            want = next((v for v in values if int(v) > threshold))
            direct = prefix + f'    if(X:=(Dup(1)|Dup("s")),Y:={call},{condition})then Print("v {{Y}}")else Print("none")\n'
            control = prefix + f'    if(Y:=({literal}),{condition})then Print("v {{Y}}")else Print("none")\n'
            specs.append((name + '-first', direct, control, 'v ' + want + '\n'))
            direct = prefix + f'    O:=option{{X:=(Dup(1)|Dup("s")),Y:={call},{condition};Y}}\n    Print("v {{O? or -1}}")\n'
            control = prefix + f'    O:=option{{Y:=({literal}),{condition};Y}}\n    Print("v {{O? or -1}}")\n'
            specs.append((name + '-option', direct, control, 'v ' + want + '\n'))
    effects = 'log:=class{var Trace:string=""}\nAdd(H:log,S:string)<transacts>:void=set H.Trace=H.Trace+S\nDefault(H:log)<transacts>:int={Add(H,"D");0}\nMark(H:log,V:t where t:type)<transacts>:t={Add(H,"A");V}\nNamed(H:log)<transacts>:int={Add(H,"N");3}\na:=class:\n    M(H:log,N:int,?Other:int=Default(H))<transacts>:int=(N+Other)|(N+Other+1)\n    M(H:log,S:string,?Other:int=Default(H))<transacts>:int=(7+Other)|(8+Other)\nMake(H:log)<transacts>:a={Add(H,"R");a{}}\n'
    for supplied in [False, True]:
        call = 'Make(H).M(H,Mark(H,X)' + (',?Other:=Named(H))' if supplied else ')')
        prefix = effects + dup + 'Main()<transacts>:void=\n    H:=log{}\n'
        body = '{Add(H,"B");Print("y {Y}")}'
        direct = prefix + f'    for(X:=(Dup(1)|Dup("s")),Y:={call})' + body + '\n    Print("trace {H.Trace}")\n'
        control = prefix + f'    for(X:=Dup(1),Y:={call})' + body + '\n' + f'    for(X:=Dup("s"),Y:={call})' + body + '\n    Print("trace {H.Trace}")\n'
        values = [4, 5, 4, 5, 10, 11, 10, 11] if supplied else [1, 2, 1, 2, 7, 8, 7, 8]
        expected = ''.join((f'y {v}\n' for v in values)) + 'trace ' + ('RANBB' if supplied else 'RADBB') * 4 + '\n'
        specs.append(('named-supplied-effects' if supplied else 'named-omitted-effects', direct, control, expected))
    for name, decl, call, values in [('generic-override', generic_class + 'up(t:type):=class(box(t)):\n    M<override>(N:int)<transacts>:t=Value|Value|Value\n    M<override>(S:string)<transacts>:t=Value|Value|Value\n', 'up(string){Value:="v"}.M(X)', ['v'] * 12), ('interface-dispatch', 'iface:=interface:\n    M(N:int)<transacts>:int\n    M(S:string)<transacts>:int\na:=class(iface):\n    M<override>(N:int)<transacts>:int=N|N+1\n    M<override>(S:string)<transacts>:int=7|8\nMake()<transacts>:iface=a{}\n', 'Make().M(X)', ['1', '2', '1', '2', '7', '8', '7', '8']), ('interface-default', 'iface:=interface:\n    M(N:int)<transacts>:int=N|N+1\n    M(S:string)<transacts>:int=7|8\na:=class(iface){}\nMake()<transacts>:iface=a{}\n', 'Make().M(X)', ['1', '2', '1', '2', '7', '8', '7', '8'])]:
        prefix = decl + dup + 'Main()<transacts>:void=\n'
        direct = prefix + f'    for(X:=(Dup(1)|Dup("s")),Y:={call}){{Print("y {{Y}}")}}\n'
        control = prefix + f'    for(X:=Dup(1),Y:={call}){{Print("y {{Y}}")}}\n' + f'    for(X:=Dup("s"),Y:={call}){{Print("y {{Y}}")}}\n'
        specs.append((name, direct, control, ''.join(('y ' + v + '\n' for v in values))))
    call = 'Make(H).M(H,Mark(H,X))'
    prefix = effects + dup + 'Main()<transacts>:void=\n    H:=log{}\n'
    for name, predicate, want, trace in [('zero', 'N>2', 0, 'RAD' * 4), ('some', 'N>1', 8, 'RADBB' * 4)]:
        body = 'block{Add(H,"B");Y}'
        direct = prefix + f'    Rows:=for(X:=(Dup(1)|Dup("s")),Y:={call},N:=1..2,{predicate}):' + body + '\n    Print("rows {Rows.Length}")\n    Print("trace={H.Trace}")\n'
        control = prefix + f'    Left:=for(X:=Dup(1),Y:={call},N:=1..2,{predicate}):' + body + '\n' + f'    Right:=for(X:=Dup("s"),Y:={call},N:=1..2,{predicate}):' + body + '\n    Print("rows {Left.Length+Right.Length}")\n    Print("trace={H.Trace}")\n'
        specs.append(('suffix-' + name, direct, control, f'rows {want}\ntrace={trace}\n'))
    body = '{Add(H,"B");Print("v {Y}")}'
    direct = prefix + f'    if(X:=(Dup(1)|Dup("s")),Y:={call},Y>6)then ' + body + ' else Print("none")\n    Print("trace={H.Trace}")\n'
    control = prefix + f'    if(X:=Dup(1),Y:={call},Y>6)then ' + body + '\n    else:\n' + f'        if(X:=Dup("s"),Y:={call},Y>6)then ' + body + ' else Print("none")\n    Print("trace={H.Trace}")\n'
    specs.append(('first-failed-prefix', direct, control, 'v 7\ntrace=RADB\n'))
    direct = prefix + f'    O:=option{{X:=(Dup(1)|Dup("s")),Y:={call},Y>6;Add(H,"B");Y}}\n    Print("v {{O? or -1}}")\n    Print("trace={{H.Trace}}")\n'
    control = prefix + f'    Left:=option{{X:=Dup(1),Y:={call},Y>6;Add(H,"B");Y}}\n    if(V:=Left?)then Print("v {{V}}")\n    else:\n' + f'        Right:=option{{X:=Dup("s"),Y:={call},Y>6;Add(H,"B");Y}}\n        Print("v {{Right? or -1}}")\n    Print("trace={{H.Trace}}")\n'
    specs.append(('option-failed-prefix', direct, control, 'v 7\ntrace=RADB\n'))
    return specs
