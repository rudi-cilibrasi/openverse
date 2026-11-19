#!/usr/bin/env python3
"""Independent cancellation traces for an owner returning inside Signal, and
for a cancelled task's children (#724)."""
from pathlib import Path
import importlib.util

ROOT = Path(__file__).resolve().parents[2]


def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts/models' / (name + '.py'))
    model = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(model)
    return model


def returning_owner(model, finish, late_child=False, wrapped=False):
    st = model.St
    active = [st('defer', label='active cleanup'), st('sleep', d='0.1'),
              st('signal', evar='E', val='X'), st('print', label='after signal')]
    if late_child:
        child = [st('defer', label='late cleanup')]
        if late_child == 2:
            child += [st('branch', body=[st('defer', label='grandchild cleanup'),
                                        st('sleep', d='1.0'), st('print', label='wrong grandchild')])]
        child += [st('sleep', d='1.0'), st('print', label='wrong child')]
        active += [st('branch', body=child)]
        if late_child == 2:
            active += [st('branch', body=[st('defer', label='sibling cleanup'),
                                         st('sleep', d='1.0'), st('print', label='wrong sibling')])]
    if not finish:
        active += [st('sleep', d='1.0'), st('print', label='wrong active')]
    other = [st('defer', label='other cleanup'), st('sleep', d='1.0'),
             st('print', label='wrong other')]
    if wrapped:
        other = [st('defer', label='other cleanup'), st('sleep', d='0.0')]
    rush = st('conc', kind='rush', var='R', pick=0, arms=[(active, 'X'), (other, 'X')])
    start = [rush] if wrapped else [st('branch', body=[rush, st('print', label='after rush')])]
    body = [st('defer', label='owner cleanup'), st('event', evar='E', sticky=False)] + start + [
        st('evawait', evar='E', var='V'), st('print', label='owner done')]
    fn = model.Fn('Owner', body, 'X')
    model.S = model.Sched()

    def main():
        yield from model.m_call(fn, {'X': 1, 'Y': 1, 'N': 0, 'Tag': 'probe'})
        model.S.p('main continued')
        yield from model.m_sleep('1.0')
        model.S.p('main done')

    code = model.S.run(main())
    # (#724) the owner's return stops nothing: the rush's arm that goes on
    # is a child of the task whose code ran the rush (the branch, or Main's
    # when wrapped), stopped when that task ends, after its own defers; a
    # task's children go newest first, each its own defers, then its own
    # children (traces checked against openverse's lowering, Lean and C)
    late = {0: [], 1: ['late cleanup'],
            2: ['sibling cleanup', 'late cleanup', 'grandchild cleanup']}[late_child]
    if wrapped and finish:
        expected = ['other cleanup', 'owner done', 'owner cleanup', 'main continued', 'after signal',
                    'active cleanup'] + late + ['main done']
    elif wrapped:
        expected = ['other cleanup', 'owner done', 'owner cleanup', 'main continued', 'after signal',
                    'main done', 'active cleanup'] + late
    elif finish:
        expected = ['owner done', 'owner cleanup', 'main continued', 'after signal', 'active cleanup'] + late + [
            'after rush', 'other cleanup', 'main done']
    else:
        expected = ['owner done', 'owner cleanup', 'main continued', 'after signal', 'wrong other',
                    'other cleanup', 'after rush', 'active cleanup'] + late + ['main done']
    expected = [e if e.startswith('main') else 'probe ' + e + ' 0' for e in expected]
    assert code == 0, (code, model.S.out)
    assert model.S.out == expected, (finish, late_child, wrapped, model.S.out, expected)
    assert all(r.done for r in model.S.roots), 'a child outlived its task'
    assert all(n == 0 for n in model.S.sleepers.values()), 'cancelled timer remained registered'


def outside_cancel_order(model):
    """A cancelled task unwinds its code (its defers), then stops its
    children, newest first, each the same way (#724): what a function
    started is its task's, not stopped with the function."""
    st = model.St

    def branch_a():
        return st('branch', body=[st('defer', label='A defer'), st('sleep', d='0.1'),
            st('branch', body=[st('defer', label='A.1 defer'), st('sleep', d=150)]),
            st('sleep', d=150)])

    f = model.Fn('F', [st('defer', label='F defer'), branch_a(),
        st('branch', body=[st('defer', label='B defer'), st('sleep', d=150)]),
        st('sleep', d=150)], 'X')
    g = model.Fn('G', [st('defer', label='G defer'), branch_a(),
        st('conc', kind='rush', var='R', pick=0, arms=[
            ([st('defer', label='r1 defer'),
              st('branch', body=[st('defer', label='r1.b defer'), st('sleep', d=150)]),
              st('sleep', d=150)], 'X'),
            ([st('defer', label='r2 defer'), st('sleep', d=150)], 'X')])], 'X')
    args = {'X': 1, 'Y': 1, 'Tag': '', 'N': 0}
    model.S = model.Sched()

    def h():
        try:
            yield from model.m_call(g, args)
        finally:
            model.S.p('H defer')

    def main():
        task = model.m_spawn(model.m_call(f, args))
        yield from model.m_sleep('1.0')
        model.m_cancel(task)
        model.S.p('cancelled F')
        task = model.m_spawn(h())
        yield from model.m_sleep('1.0')
        model.m_cancel(task)
        model.S.p('cancelled H')

    assert model.S.run(main()) == 0
    actual = [line.removesuffix(' 0').strip() for line in model.S.out]
    expected = ['F defer', 'B defer', 'A defer', 'A.1 defer', 'cancelled F',
                'r2 defer', 'r1 defer', 'r1.b defer', 'G defer',
                'H defer', 'A defer', 'A.1 defer', 'cancelled H']
    assert actual == expected, (actual, expected)
    assert all(n == 0 for n in model.S.sleepers.values()), 'cancelled timer remained registered'


for name in ['sched_gen', 'sched_gen2']:
    for finish in [False, True]:
        for late_child in [0, 1, 2]:
            for wrapped in [False, True]:
                returning_owner(load(name), finish, late_child, wrapped)
    outside_cancel_order(load(name))
print('scheduler-model: both models preserve active arms and late children (26 traces)')
