from typing import List, Optional, Set, FrozenSet, Union, Tuple, Dict
from itertools import chain

from pysmt.environment import Environment as PysmtEnv
from pysmt.logics import AUTO
from pysmt.fnode import FNode
from pysmt.exceptions import SolverReturnedUnknownResultError

try:
    from pysmt.solvers.z3 import Z3Solver
except ImportError:
    from solver import Z3Solver

from solver import Solver, solve_with_timeout, get_solvers
from rationalapprox import RationalApprox
from utils import log

_TIMEOUT = 20
_MAX_LOOPS = 20
_EF_APPROX = True
_EF_SOLVER_LOG_LVL = 1


def set_ef_approximate(val: bool) -> None:
    assert isinstance(val, bool)
    global _EF_APPROX
    _EF_APPROX = val


def get_ef_approximate() -> bool:
    global _EF_APPROX
    return _EF_APPROX


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


def set_log_lvl(val: int) -> None:
    assert isinstance(val, int)
    global _EF_SOLVER_LOG_LVL
    _EF_SOLVER_LOG_LVL = val


def get_log_lvl() -> int:
    global _EF_SOLVER_LOG_LVL
    return _EF_SOLVER_LOG_LVL


def efmultisolve(env, x1: Union[Set[FNode], FrozenSet[FNode]],
                 x2: Optional[Union[Set[FNode], FrozenSet[FNode]]],
                 phi: FNode, logic=AUTO, impl=None) \
        -> Tuple[Union[Dict[FNode, FNode], Optional[bool]],
                 List[FNode]]:
    mgr = env.formula_manager
    if x2 is None:
        x2 = env.fvo.get_free_variables(phi) - x1
    learn = []
    for name in reversed(get_solvers()):
        log(f"\tEF-SMT using solver: {name}.", get_log_lvl())
        res, _learn = efsolve(env, x1, x2, phi, logic=logic,
                              esolver_name=name, fsolver_name=name,
                              impl=impl)
        learn.extend(_learn)
        if res is not None:
            return res, learn
        if len(_learn) > 0:
            phi = mgr.And(phi, mgr.And(_learn))
    return None, learn


def efsolve(env, x1: Union[Set[FNode], FrozenSet[FNode]],
            x2: Union[Set[FNode], FrozenSet[FNode]],
            phi: FNode, logic=AUTO,
            esolver_name: Optional[str] = None,
            fsolver_name: Optional[str] = None,
            impl=None) \
        -> Tuple[Union[Dict[FNode, FNode], Optional[bool]],
                 List[FNode]]:
    """Solves exists x1. forall x2. phi(x1, x2)"""
    assert isinstance(env, PysmtEnv)
    assert isinstance(x1, (set, frozenset))
    assert all(s in env.formula_manager.get_all_symbols()
               for s in x1)
    assert isinstance(phi, FNode)
    assert esolver_name is None or isinstance(esolver_name, str)
    assert fsolver_name is None or isinstance(fsolver_name, str)
    assert isinstance(x2, (set, frozenset))
    assert all(s in env.formula_manager.get_all_symbols()
               for s in x1 | x2)
    assert x1 | x2 >= env.fvo.get_free_variables(phi)

    mgr = env.formula_manager
    if len(x1) == 0:
        assert x2 >= env.fvo.get_free_variables(phi)
        with Solver(env=env, logic=logic,
                    name=fsolver_name) as solver:
            solver.add_assertion(mgr.Not(phi))
            try:
                sat = solve_with_timeout(get_timeout(), solver)
            except SolverReturnedUnknownResultError:
                sat = None
            if sat is None:
                log("\t\tEF-SMT E-timeout.", get_log_lvl())
                return None, []
            if sat is False:
                return {}, []
            return False, []

    simplify = env.simplifier.simplify
    substitute = env.substituter.substitute
    learn: List[FNode] = []

    approx = None
    if get_ef_approximate():
        approx = RationalApprox()

    with Solver(env=env, logic=logic, name=esolver_name) as esolver, \
         Solver(env=env, logic=logic, name=fsolver_name) as fsolver:
        esolver.add_assertion(phi)
        loops = 0
        while get_maxloops() < 0 or loops <= get_maxloops():
            loops += 1
            esolver.push()
            try:
                eres = solve_with_timeout(get_timeout(), esolver)
            except SolverReturnedUnknownResultError:
                eres = None

            if eres is not True:
                if eres is None:
                    log("\t\tEF-SMT E-timeout.", get_log_lvl())
                else:
                    assert eres is False
                    log("\t\tEF-SMT found UNSAT.", get_log_lvl())
                return False, learn

            # eres is True
            assert eres is True
            emodel = esolver.get_model()
            if approx:
                eval_phi: Optional[bool] = False
                for x, val in esolver.get_values(chain(x1, x2)).items():
                    if val.is_bool_constant():
                        eq = x if val.is_true() else mgr.Not(x)
                    else:
                        new_val = approx(val.constant_value())
                        if val.is_real_constant():
                            new_val = mgr.Real(new_val)
                        else:
                            assert val.is_int_constant()
                            new_val = mgr.Int(int(new_val))
                        eq = mgr.Equals(x, new_val)
                    esolver.add_assertion(eq)
                try:
                    eval_phi = solve_with_timeout(get_timeout(),
                                                  esolver)
                except SolverReturnedUnknownResultError:
                    eval_phi = None
                    esolver.reset_assertions()
                    esolver.add_assertion(phi)
                    for constr in learn:
                        esolver.add_assertion(constr)
                    esolver.push()

                if eval_phi is True:
                    emodel = esolver.get_model()
                else:
                    log(f"\t\tEF-SMT, iteration {loops}: "
                        "E-model simplification failed.",
                        get_log_lvl() + 2)
                    # complex model more `expensive`, quit sooner.
                    loops += 5
                    # return None, learn

            x1_model = emodel.get_values(x1)
            fsolver.add_assertion(mgr.Not(simplify(substitute(phi, x1_model))))

            try:
                fres = solve_with_timeout(get_timeout(), fsolver)
            except SolverReturnedUnknownResultError:
                fres = None

            if fres is None:
                log("\t\tEF-SMT F-timeout.", get_log_lvl())
                return None, learn

            if fres is False:
                # EF query valid. Return assignment for existential vars.
                return x1_model, learn
            # try generalise formula based on model
            x2_model = fsolver.get_values(x2)
            if isinstance(fsolver, Z3Solver):
                x2_model = filter_irrationals(env, x2_model)
                if x2_model is None:
                    log("\t\tEF-solver cannot handle irrational in Z3 model.",
                        get_log_lvl())
                    return None, learn
            if __debug__:
                with Solver(env=env) as _solver:
                    _solver.add_assertion(substitute(substitute(phi, x1_model),
                                                     x2_model))
                    assert _solver.solve() is False
                del _solver

            sub_phi = simplify(substitute(phi, x2_model))
            if sub_phi.is_false():
                # There exist no x1 making phi true for x2_model.
                return False, learn
            assert not sub_phi.is_true()
            fsolver.reset_assertions()
            assert len(fsolver.assertions) == 0
            if impl is not None and \
               simplify(substitute(phi, x1_model)).is_false():
                sub_phi = impl([mgr.Not(sub_phi)], emodel, {})
                sub_phi = mgr.Not(mgr.And(sub_phi))
            assert sub_phi in mgr.formulae.values()
            esolver.pop()  # remove approximated assignments.
            learn.append(sub_phi)
            esolver.add_assertion(sub_phi)

        log("\t\tEF-solver reached max number of iterations.", get_log_lvl())
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


def efesolve(env,
             x0: Union[Set[FNode], FrozenSet[FNode]],
             x1: Union[Set[FNode], FrozenSet[FNode]],
             x2: Union[Set[FNode], FrozenSet[FNode]],
             phi: FNode, logic=AUTO,
             esolver_name: Optional[str] = None,
             fsolver_name: Optional[str] = None,
             impl=None) \
        -> Tuple[Union[Dict[FNode, FNode], Optional[bool]],
                 List[FNode]]:
    """Solves exists x0. forall x1. exists x2. phi(x1, x2)"""
    assert isinstance(env, PysmtEnv)
    assert isinstance(x0, (set, frozenset))
    assert isinstance(x1, (set, frozenset))
    assert isinstance(x2, (set, frozenset))
    assert all(s in env.formula_manager.get_all_symbols()
               for s in x0 | x1 | x2)
    assert x0 | x1 | x2 >= env.fvo.walk(phi)
    assert isinstance(phi, FNode)
    assert esolver_name is None or isinstance(esolver_name, str)
    assert fsolver_name is None or isinstance(fsolver_name, str)

    mgr = env.formula_manager
    simplify = env.simplifier.simplify
    substitute = env.substituter.substitute
    learn: List[FNode] = []

    # approx = None
    # if approximate():
    #     approx = RationalApprox()

    with Solver(env=env, logic=logic, name=fsolver_name) as esolver:
        esolver.add_assertion(phi)

        loops = 0
        while get_maxloops() < 0 or loops <= get_maxloops() * 5:
            loops += 1

            esolver.push()
            try:
                eres = solve_with_timeout(get_timeout(), esolver)
            except SolverReturnedUnknownResultError:
                eres = None

            if eres is not True:
                if eres is None:
                    log("\t\tEFE-SMT E-timeout.", get_log_lvl())
                else:
                    assert eres is False
                    log("\t\tEFE-SMT found UNSAT.", get_log_lvl())
                return eres, learn

            # eres is True
            assert eres is True
            x0_model = esolver.get_values(x0)
            x2_model = esolver.get_values(x2)
            sub_phi = simplify(substitute(phi, x0_model))
            x1_model, _ = efsolve(env, x1, x2, mgr.Not(sub_phi), logic=logic,
                                  esolver_name=esolver_name,
                                  fsolver_name=fsolver_name,
                                  impl=impl)
            if x1_model is False:
                return x0_model, learn  # found assignment.
            if x1_model is None:
                return None, learn  # unknown.
            assert isinstance(x1_model, dict)
            assert frozenset(x1_model.keys()) == x1
            # replace assignments x1 and x2 in phi.
            sub_phi = simplify(substitute(
                phi,
                dict(chain(x1_model.items(),
                           ((k, x2_model[k]) for k in x2)))))
            assert not sub_phi.is_true()
            if not sub_phi.is_false() and impl:
                sub_phi = impl([mgr.Not(sub_phi)], esolver, {})
                sub_phi = mgr.Not(mgr.And(sub_phi))
            assert sub_phi in mgr.formulae.values()
            learn.append(sub_phi)
            esolver.add_assertion(sub_phi)

        log("\t\tEFE-solver reached max number of iterations.", get_log_lvl())
        return None, learn
