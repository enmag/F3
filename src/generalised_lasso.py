from typing import Tuple, Optional, FrozenSet, Dict, List

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode

from rewritings import TimesDistributor
from ineq import Ineq
from utils import symb_to_next, symb_is_next, symb_to_curr, symb_is_curr


def is_generalised_lasso(env: PysmtEnv, loop: List[Dict[FNode, FNode]],
                         symbols: FrozenSet[FNode],
                         trans: FNode,
                         td: TimesDistributor) -> Tuple[bool,
                                                        Optional[FrozenSet[FNode]],
                                                        Optional[FrozenSet[FNode]]]:
    assert isinstance(env, PysmtEnv)
    assert isinstance(loop, list)
    assert all(isinstance(state, dict) for state in loop)
    assert all(isinstance(k, FNode) for state in loop for k in state)
    assert all(k in symbols for state in loop for k in state)
    assert all(isinstance(v, FNode)
               for state in loop for v in state.values())
    assert all(v in env.formula_manager.formulae.values()
               for state in loop for v in state.values())
    assert isinstance(symbols, frozenset)
    assert all(s in env.formula_manager.get_all_symbols()
               for s in symbols)
    assert isinstance(trans, FNode)
    assert trans in env.formula_manager.formulae.values()
    assert isinstance(td, TimesDistributor)

    mgr = env.formula_manager
    subst = env.substituter.substitute
    simpl = env.simplifier.simplify
    conc_lasso_symbs = frozenset(s for s in symbols
                                 if loop[0][s] == loop[-1][s])
    conc_assigns = [{s: state[s] for s in conc_lasso_symbs}
                    for state in loop]
    for idx in range(0, len(loop)):
        x_idx = (idx + 1) % len(loop)
        x_state = loop[x_idx]
        for s in conc_lasso_symbs:
            x_s = symb_to_next(mgr, s)
            conc_assigns[idx][x_s] = x_state[s]
    preds = frozenset(filter(lambda e: not e.is_true() and not e.is_false(),
                             (simpl(subst(p, assign)) for assign in conc_assigns
                              for s in symbols for p in env.ao.get_atoms(trans))))
    assert all(env.fvo.walk(p) <= (symbols - conc_lasso_symbs) |
               frozenset(symb_to_next(mgr, s)
                         for s in symbols - conc_lasso_symbs)
               for p in preds), (preds, symbols - conc_lasso_symbs)
    pos_diverging = set()
    neg_diverging = set()
    for p in preds:
        p = Ineq(env, p, [], td)
        p_vars = list(p.lhs.keys())
        if not all(v.is_symbol() for v in p_vars):
            return False, None, None
        if len(p_vars) == 1 and p.is_le() or p.is_lt():
            var = p_vars[0]
            coef = p.lhs[var].pysmt_expr().constant_value()
            if symb_is_next(var):
                var = symb_to_curr(mgr, var)
            if coef > 0:
                if var in pos_diverging:
                    return False, None, None
                neg_diverging.add(var)
            elif coef < 0:
                if var in neg_diverging:
                    return False, None, None
                pos_diverging.add(var)
        elif len(p_vars) == 2:
            c_var = p_vars[0]
            x_var = p_vars[1]
            if (symb_is_curr(c_var) and symb_is_curr(x_var)) or \
               (symb_is_next(c_var) and symb_is_next(x_var)):
                return False, None, None
            if symb_is_next(c_var):
                c_var, x_var = x_var, c_var
            if symb_to_next(mgr, c_var) != x_var:
                return False, None, None
            x_coef = p.lhs[x_var].pysmt_expr().constant_value()
            c_coef = -1*p.lhs[c_var].pysmt_expr().constant_value()
            const = simpl(p.rhs.pysmt_expr()).constant_value()
            if p.is_eq():
                if x_coef < 0:
                    c_coef = - c_coef
                    const = - const
                if c_coef < 0:
                    return False, None, None
                if const > 0:
                    if c_var in neg_diverging:
                        return False, None, None
                    pos_diverging.add(c_var)
                elif const < 0:
                    if c_var in pos_diverging:
                        return False, None, None
                    neg_diverging.add(c_var)
            elif x_coef > 0:
                if c_var in pos_diverging:
                    return False, None, None
                neg_diverging.add(c_var)
            elif x_coef < 0:
                if c_var in neg_diverging:
                    return False, None, None
                pos_diverging.add(c_var)
        else:
            return False, None, None
    return True, frozenset(pos_diverging), frozenset(neg_diverging)
