#!/usr/bin/env bash
# A source profile must reject before execution/emission, without changing admitted code.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
python3 - "$root" <<'PY'
import pathlib, subprocess, sys, tempfile

root = pathlib.Path(sys.argv[1])
ov, cv = root / '.lake/build/bin/openverse', root / 'runtime/build/cverse'
checks = 0

def run(*args):
    return subprocess.run([str(ov), *map(str, args)], capture_output=True, text=True, timeout=30)

def require(condition, detail):
    global checks
    checks += 1
    if not condition:
        raise AssertionError(detail)

with tempfile.TemporaryDirectory(prefix='openverse profile ') as directory:
    tmp = pathlib.Path(directory)
    def source(name, text):
        path = tmp / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text + '\n')
        return path

    positive = {
        'failure': '''Pos(X:int)<computes><decides>:int =
    X>0
    X
Main():void =
    if(X:=Pos[3])then Print("ok {X}")else Print("bad")
    if(X:=Pos[-1])then Print("bad")else Print("failed")''',
        'mutation': '''Main():void =
    var N:int=0
    loop:
        set N+=1
        if(N=3):break
    Print("count {N}")''',
        'function-value': '''first(X:int):int=X+1
Apply(F:type{_(:int):int},X:int):int=F(X)
Main():void=Print("{Apply(first,3)} | first for 1..2")''',
        'dispatch': '''base(t:type):=class:
    V:t
    Get(?X:t=V):t=X
child(u:type):=class(base(u)):
    Get<override>(?X:u=V):u=X
Read(B:base(t) where t:type):t=B.Get()
Main():void=Print("{Read(child(int){V:=7})}")''',
        'refinement': '''pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){C:int=4}
Read(P:pair(a,b) where a:type,b:type):int=if(D:=dup[P])then D.C else 0
Main():void=Print("{Read(dup(int){A:=1,B:=2})}")''',
        'scheduler': '''Wait(N:int)<suspends>:int=
    Sleep(0.0)
    Print("wait {N}")
    N
Main()<suspends>:void=
    T:=spawn{Wait(3)}
    Print("start")
    V:=T.Await()
    Print("done {V}")''',
        'defaults': '''item(t:type):=struct{V:t}
Make(X:t,?B:item(t)=item{V:=X} where t:type):t=B.V
Main():void=Print(Make("default"))''',
        'method-value': '''box(t:type,u:type):=class:
    V:t
    Extra:u
    Array(X:[]t):[]t=X
    Size():int=3
Run(B:box(a,b) where a:type,b:type):int=
    F:=B.Array
    G:=B.Size
    F(array{}).Length+G()
Main():void=Print("{Run(box(int,string){V:=7,Extra:="s"})}")''',
        'open-function-value': '''Id(X:t where t:type):t=X
Bind(X:t where t:type):type{_(:t):t}=Id
Main():void=
    F:=Bind(7)
    Print("{F(9)}")''',
        'open-tuple-value': '''Id(X:t where t:type)<computes>:t=X
Run(X:t,Y:u where t:type,u:type)<computes>:tuple(t,u)=
    F:type{_(:t,:u)<computes>:tuple(t,u)}=Id
    F(X,Y)
Main():void=
    R:=Run(7,"s")
    Print("{R(0)} {R(1)}")''',
        'method-instance': '''box(t:type):=class:
    V:t
    Same(X:u where u:type):u=X
Bind(B:box(t),X:u where t:type,u:type):type{_(:u):u}=B.Same
Main():void=
    F:=Bind(box(string){V:="s"},7)
    Print("{F(9)}")''',
    }
    for name, text in positive.items():
        path = source(f'{name}.verse', text)
        full, strict = tmp / 'full.vbc', tmp / 'strict.vbc'
        a = run('run', path, '--emit', full)
        b = run('run', path, '--no-choice', '--emit', strict)
        require(a.returncode == 0, (name, 'normal mode', a.stderr))
        require((b.stdout, b.stderr, b.returncode) == (a.stdout, a.stderr, a.returncode), (name, b))
        require(full.read_bytes() == strict.read_bytes(), (name, 'profile changed bytecode'))
        c = subprocess.run([str(cv), str(strict)], capture_output=True, text=True, timeout=30)
        require((c.stdout, c.stderr, c.returncode) == (a.stdout, a.stderr, a.returncode), (name, c))
        for command in ('check', 'core'):
            a, b = run(command, path), run(command, path, '--no-choice')
            require(a.returncode == 0 and (a.stdout, a.stderr, a.returncode) ==
                    (b.stdout, b.stderr, b.returncode), (name, command, b))

    negative = {
        'pipe': ('Main():void=if(X:=1|2)then Print("{X}")', 'choice (|)'),
        'dead': ('Main():void=if(false?)then block{if(X:=1|2)then Print("{X}")}else Print("ok")', 'choice (|)'),
        'first': ('Main():void=Print("{first{3}}")', 'first-success'),
        'first-body': ('Main():void=Print("{first(X:=3){X+1}}")', 'first-success'),
        'for': ('Main():void=Print("{(for(X:array{1,2}):X).Length}")', 'for consumers'),
        'for-macro': ('Main():void=Print("{for{X:array{1,2};X}.Length}")', 'for consumers'),
        'range': ('Main():void=Print("{(for(X:=1..2):X).Length}")', 'for consumers'),
        'callee': ('Pick():int=1|2\nCall():int=Pick()\nMain():void=if(X:=Call())then Print("{X}")', 'choice (|)'),
        'method': ('box:=class{Pick():int=1|2}\nMain():void=if(X:=box{}.Pick())then Print("{X}")', 'choice (|)'),
        'named-default': ('Pick(?X:int=block{if(Y:=1|2)then Y else 0}):int=X\nMain():void=Print("{Pick()}")', 'choice (|)'),
        'struct-default': ('box:=struct{X:int=block{if(Y:=1|2)then Y else 0}}\nMain():void=if(B:=option{box{}}?)then Print("{B.X}")', 'choice (|)'),
        'class-default': ('box:=class{X:int=block{if(Y:=1|2)then Y else 0}}\nMain():void=if(B:=option{box{}}?)then Print("{B.X}")', 'choice (|)'),
        'constructor': ('box:=class{X:int=0}\nMake<constructor>():=box{X:=block{if(Y:=1|2)then Y else 0}}\nMain():void=Print("{Make().X}")', 'choice (|)'),
        'function-choice': ('A(X:int):int=X\nB(X:int):int=X+1\nMain():void=if(F:type{_(:int):int}=A|B)then Print("{F(3)}")', 'choice (|)'),
    }
    for name, (text, diagnostic) in negative.items():
        path = source(f'{name}-reject.verse', text)
        normal = run('check', path)
        require(normal.returncode == 0, (name, 'normal fixture must be valid', normal.stderr))
        for command in ('check', 'core', 'run', 'emit'):
            output = tmp / 'rejected.vbc'
            output.unlink(missing_ok=True)
            args = [command, path, '--no-choice']
            if command == 'run': args += ['--emit', output]
            if command == 'emit': args += ['-o', output]
            r = run(*args)
            require(r.returncode == 4 and not r.stdout and '--no-choice excludes ' in r.stderr
                    and diagnostic in r.stderr and f'{path}:' in r.stderr, (name, command, r))
            require(not output.exists(), (name, command, 'rejected code was emitted'))

    # Imports are checked even when the excluded definition is never called.
    source('imports/hidden.verse', 'Unused():int=1|2')
    imported = source('imports/main.verse', 'using{"hidden.verse"}\nMain():void=Print("unused")')
    r = run('run', imported, '--no-choice')
    require(r.returncode == 4 and not r.stdout and 'hidden.verse:1:' in r.stderr, r)
    # File-backed values and directory loading must pass the same admission gate.
    source('directory/Pick.value', 'first{1}')
    source('directory/Self.verse', 'Main():void=Print("{Pick}")')
    r = run('check', tmp / 'directory', '--no-choice')
    require(r.returncode == 4 and 'Pick.value:1:' in r.stderr and 'first-success' in r.stderr, r)

    args = source('args.verse', '''Main():void=
    Print("args {Args.Length}")
    if(X:=Args[0])then Print(X)
    if(X:=Args[1])then Print(X)''')
    for invocation in [
        ['--no-choice', 'run', args],
        ['run', '--no-choice', args],
        ['run', args, '--no-choice'],
        ['run', args, '--fuel', '100000', '--no-choice'],
        ['--no-choice', 'run', '--no-choice', args, '--no-choice'],
    ]:
        r = run(*invocation)
        require(r.returncode == 0 and r.stdout == 'args 0\n', (invocation, r))
    for command in ('check', 'core'):
        for invocation in [['--no-choice', command, args], [command, '--no-choice', args]]:
            require(run(*invocation).returncode == 0, invocation)
    for invocation in [
        ['run', args, '--no-choice', 'hello'],
        ['run', args, '--no-choice', '--', '--no-choice', 'do'],
        ['run', args, 'hello', '--no-choice'],
    ]:
        r = run(*invocation)
        expected = ('args 1\nhello\n' if invocation[-1] == 'hello' else
                    'args 2\n--no-choice\ndo\n' if '--' in invocation else 'args 2\nhello\n--no-choice\n')
        require(r.returncode == 0 and r.stdout == expected, (invocation, r))

    entry = source('entry.verse', 'Main():void=Print("must not run")')
    for command in ('run', 'emit'):
        output = tmp / 'entry.vbc'
        output.write_bytes(b'keep existing output')
        invocation = [command, entry, '--no-choice']
        invocation += ['--emit', output] if command == 'run' else ['-o', output]
        r = run(*invocation, 'do', 'first{1}')
        require(r.returncode == 4 and not r.stdout and 'first-success' in r.stderr, r)
        require(output.read_bytes() == b'keep existing output', 'rejection clobbered output')
    r = run('run', entry, '--no-choice', 'do', 'Print("literal | first for")')
    require(r.returncode == 0 and r.stdout == 'literal | first for\n', r)
    for invocation in [
        ['emit', '--no-choice', args, '-o', tmp / 'args.vbc', 'hello'],
        ['emit', args, '-o', tmp / 'args.vbc', '--no-choice', 'hello'],
    ]:
        r = run(*invocation)
        require(r.returncode == 0 and not r.stdout, (invocation, r))
        c = subprocess.run([str(cv), str(tmp / 'args.vbc')], capture_output=True, text=True)
        require(c.returncode == 0 and c.stdout == 'args 1\nhello\n', c)

print(f'choice-profile: {checks} checks passed')
PY
