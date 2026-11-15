#!/usr/bin/env python3
"""Independent cancellation traces for an owner returning inside Signal."""
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
    expected = (['probe other cleanup 0', 'probe owner done 0', 'probe owner cleanup 0'] if wrapped else
                ['probe owner done 0', 'probe owner cleanup 0', 'probe other cleanup 0'])
    expected += ['main continued', 'probe after signal 0']
    late_cleanup = (['probe sibling cleanup 0', 'probe grandchild cleanup 0'] if late_child == 2 else []) + ['probe late cleanup 0']
    if late_child and not finish:
        expected += late_cleanup
    expected += ['probe active cleanup 0']
    if late_child and finish:
        expected += late_cleanup
    if finish and not wrapped:
        expected += ['probe after rush 0']
    expected += ['main done']
    assert code == 0, (code, model.S.out)
    assert model.S.out == expected, (finish, model.S.out, expected)
    assert len(model.S.roots) == (4 if late_child == 2 else 2 if late_child else 1) and all(r.done for r in model.S.roots), 'cancelled arms or children became live roots'
    assert all(n == 0 for n in model.S.sleepers.values()), 'cancelled timer remained registered'


for name in ['sched_gen', 'sched_gen2']:
    for finish in [False, True]:
        for late_child in [0, 1, 2]:
            for wrapped in [False, True]:
                returning_owner(load(name), finish, late_child, wrapped)
print('scheduler-model: both models preserve active arms and late children (24 traces)')
