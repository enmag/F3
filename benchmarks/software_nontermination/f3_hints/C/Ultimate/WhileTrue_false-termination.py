from typing import Tuple, FrozenSet

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
import pysmt.typing as types

from utils import symb_to_next
from hint import Hint, Location

def transition_system(env: PysmtEnv) -> Tuple[FrozenSet[FNode], FNode, FNode,
                                              FNode]:
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    x_pc = symb_to_next(mgr, pc)

    symbols = frozenset([pc])

    m_1 = mgr.Int(-1)

    n_locs = 1
    ints = [mgr.Int(idx) for idx in range(1)]
    pcs = []
    x_pcs = []
    for idx in range(n_locs):
        num = ints[idx]
        pcs.append(mgr.Equals(pc, num))
        x_pcs.append(mgr.Equals(x_pc, num))
    pcend = mgr.Equals(pc, m_1)
    x_pcend = mgr.Equals(x_pc, m_1)

    init = pcs[0]
    cfg = []
    # pc = 0 -> pc' = 1
    cfg.append(mgr.Implies(pcs[0], x_pcs[0]))
    # pc = -1 -> pc' = -1
    cfg.append(mgr.Implies(pcend, x_pcend))

    trans = []
    trans = mgr.And(*cfg, *trans)

    fairness = mgr.Not(mgr.Equals(pc, m_1))
    return symbols, init, trans, fairness


def hints(env: PysmtEnv) -> FrozenSet[Hint]:
    assert isinstance(env, PysmtEnv)

    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    symbs = frozenset([pc])

    x_pc = symb_to_next(mgr, pc)
    i_0 = mgr.Int(0)
    l0 = Location(env, mgr.Equals(pc, i_0), mgr.TRUE())
    l0.set_progress(0, eq_0=mgr.Equals(x_pc, i_0))
    h_pc = Hint("h_pc", env, frozenset([pc]), symbs)
    h_pc.set_locs([l0])

    return frozenset([h_pc])
