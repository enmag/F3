from typing import List, Optional
from itertools import chain

from pysmt.environment import Environment as PysmtEnv
from pysmt.logics import AUTO
from pysmt.fnode import FNode
from pysmt.exceptions import SolverReturnedUnknownResultError

try:
    from pysmt.solvers.z3 import Z3Solver
except ImportError:
    from solver import Z3Solver

from solver import Solver, solve_with_timeout
from rationalapprox import RationalApprox, approximate
from generalise_path import Generaliser
from utils import to_smt2, log

_TIMEOUT = 20
_MAX_LOOPS = 20


def set_timeout(val: int) -> None:
    assert isinstance(val, int)
    global _TIMEOUT
    _TIMEOUT = val


def get_timeout() -> int:
    global _TIMEOUT
    return _TIMEOUT


def set_maxloops(val: int) -> None:
    assert isinstance(val, int)
    global _MAX_LOOPS
    _MAX_LOOPS = val


def get_maxloops() -> int:
    global _MAX_LOOPS
    return _MAX_LOOPS


_LOG_LVL0 = 1
_LOG_LVL1 = 5


def efsolve(env, x1: frozenset, x2: frozenset, phi: FNode, logic=AUTO,
            esolver_name: Optional[str] = None,
            fsolver_name: Optional[str] = None,
            generaliser: Optional[Generaliser] = None):
    """Solves exists x1. forall x2. phi(x1, x2)"""
    assert isinstance(env, PysmtEnv)
    assert isinstance(x1, frozenset)
    assert isinstance(x2, frozenset)
    assert isinstance(phi, FNode)
    assert esolver_name is None or isinstance(esolver_name, str)
    assert fsolver_name is None or isinstance(fsolver_name, str)
    assert x1 | x2 >= phi.get_free_variables()

    mgr = env.formula_manager
    simplify = env.simplifier.simplify
    substitute = env.substituter.substitute
    learn: List[FNode] = []

    approx = None
    if approximate():
        approx = RationalApprox()

    with Solver(env=env, logic=logic, name=esolver_name) as esolver, \
         Solver(env=env, logic=logic, name=fsolver_name) as fsolver:
        esolver.add_assertion(phi)
        loops = 0
        while get_maxloops() < 0 or loops <= get_maxloops():
            loops += 1
            log("\t\tEF-SMT iteration: {}".format(loops), _LOG_LVL1)

            esolver.push()
            try:
                eres = solve_with_timeout(get_timeout(), esolver)
            except SolverReturnedUnknownResultError:
                eres = None

            if eres is not True:
                if eres is None:
                    log("\t\tEF-SMT E-timeout", _LOG_LVL0)
                    log("\n{}\n".format(to_smt2(esolver.assertions)),
                        _LOG_LVL0 + 1)
                else:
                    assert eres is False
                    log("\t\tEF-SMT found UNSAT", _LOG_LVL0)
                return eres, learn

            # eres is True
            assert eres is True
            if approx:
                eval_phi: Optional[bool] = False
                x_vals = esolver.get_values(chain(x1, x2))
                for x, val in x_vals.items():
                    if val.is_bool_constant():
                        eq = x if val.is_true() \
                             else mgr.Not(x)
                    else:
                        new_val = approx(val.constant_value())
                        if val.is_real_constant():
                            new_val = mgr.Real(new_val)
                        else:
                            assert val.is_int_constant()
                            new_val = mgr.Int(int(new_val))
                        eq = mgr.Equals(x, new_val)
                    esolver.add_assertion(eq)
                del x_vals
                try:
                    eval_phi = solve_with_timeout(get_timeout(),
                                                  esolver)
                except SolverReturnedUnknownResultError:
                    eval_phi = None
                    log("\t\tEF-SMT E-model simplification timeout",
                        _LOG_LVL0)
                    log("\n{}\n".format(to_smt2(esolver.assertions)),
                        _LOG_LVL0 + 1)

                if eval_phi is not True:
                    log("\t\tEF-SMT E-model simplification failed",
                        _LOG_LVL0)
                    return None, learn

            tau = esolver.get_values(x1)

            log("\t\tEF-SMT guess: {}".format(tau), _LOG_LVL1)
            fsolver.add_assertion(mgr.Not(simplify(substitute(phi, tau))))

            try:
                fres = solve_with_timeout(get_timeout(), fsolver)
            except SolverReturnedUnknownResultError:
                fres = None

            if fres is None:
                log("\t\tEF-SMT F-timeout", _LOG_LVL0)
                log("\n{}\n".format(to_smt2(fsolver.assertions)),
                    _LOG_LVL0 + 1)
                return None, learn

            if fres is False:
                return tau, learn
            # try generalise formula based on model
            sigma = fsolver.get_values(x2)
            if isinstance(fsolver, Z3Solver):
                sigma = filter_irrationals(env, sigma)
                if sigma is None:
                    log("\t\tEF-solver cannot handle irrational in Z3 model",
                        _LOG_LVL0)

                return None, learn
            sub_phi = simplify(substitute(phi, sigma))
            if generaliser:
                sub_phi = generaliser.bool_impl([mgr.Not(sub_phi)],
                                                esolver)
                sub_phi = mgr.Not(mgr.And(sub_phi))
            assert sub_phi in mgr.formulae.values()
            learn.append(sub_phi)

            fsolver.reset_assertions()

            esolver.pop()  # remove approximated assignments.
            esolver.add_assertion(sub_phi)

        log("\t\tEF-solver reached max number of iterations", _LOG_LVL0)
        log("\n{}\n".format(to_smt2(esolver.assertions)), _LOG_LVL0 + 1)
        return None, learn


def filter_irrationals(env: PysmtEnv, model: dict) -> Optional[dict]:
    mgr = env.formula_manager
    for k, v in model.items():
        if v.is_algebraic_constant():
            v = v.constant_value()
            if v.is_rational():
                model[k] = mgr.Real((v.numerator(), v.denominator()))
            else:
                return None

    return model
