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


def returning_owner(model, finish):
    st = model.St
    active = [st('defer', label='active cleanup'), st('sleep', d='0.1'),
              st('signal', evar='E', val='X'), st('print', label='after signal')]
    if not finish:
        active += [st('sleep', d='1.0'), st('print', label='wrong active')]
    other = [st('defer', label='other cleanup'), st('sleep', d='1.0'),
             st('print', label='wrong other')]
    body = [st('defer', label='owner cleanup'), st('event', evar='E', sticky=False),
            st('branch', body=[st('conc', kind='rush', var='R', pick=0,
                                  arms=[(active, 'X'), (other, 'X')]),
                               st('print', label='after rush')]),
            st('evawait', evar='E', var='V'), st('print', label='owner done')]
    fn = model.Fn('Owner', body, 'X')
    model.S = model.Sched()

    def main():
        yield from model.m_call(fn, {'X': 1, 'Y': 1, 'N': 0, 'Tag': 'probe'})
        model.S.p('main continued')
        yield from model.m_sleep('1.0')
        model.S.p('main done')

    code = model.S.run(main())
    expected = ['probe owner done 0', 'probe owner cleanup 0',
                'probe other cleanup 0', 'main continued', 'probe after signal 0',
                'probe active cleanup 0']
    if finish:
        expected += ['probe after rush 0']
    expected += ['main done']
    assert code == 0, (code, model.S.out)
    assert model.S.out == expected, (finish, model.S.out, expected)
    assert len(model.S.roots) == 1 and model.S.roots[0].done, 'cancelled arms became roots'
    assert all(n == 0 for n in model.S.sleepers.values()), 'cancelled timer remained registered'


for name in ['sched_gen', 'sched_gen2']:
    for finish in [False, True]:
        returning_owner(load(name), finish)
print('scheduler-model: both models preserve active-arm cleanup and completion (4 traces)')
