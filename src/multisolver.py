from typing import List, Iterable, Optional
import time
from signal import signal, SIGSEGV
from types import MethodType

try:
    import mathsat
    from pysmt.solvers.msat import MathSAT5Solver
except ImportError:
    class MathSAT5Solver:
        pass

try:
    from pysmt.solvers.z3 import Z3Solver
except ImportError:
    class Z3Solver:
        pass

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
from pysmt.logics import Logic
from pysmt.exceptions import SolverReturnedUnknownResultError

from solver import get_solvers, Solver
from utils import log


class MultiSolver:
    """Keep multiple solvers synchronised,
    upon failure of one solver try using the following one"""

    def __init__(self, env: PysmtEnv, timeout: int,
                 logic: Logic = None, log_lvl: int = 5,
                 pref_vars: Optional[Iterable[FNode]] = None,
                 solver_names: Optional[List[str]] = None):
        assert isinstance(env, PysmtEnv)
        assert isinstance(timeout, int)
        assert timeout >= 0
        assert logic is None or isinstance(logic, Logic)
        assert isinstance(log_lvl, int)
        self.log_lvl = log_lvl
        self.env = env
        self.logic = logic
        self.timeout = timeout
        self._segfault = False
        self._solver_names = solver_names if solver_names else get_solvers()
        assert isinstance(self._solver_names, list)
        assert len(self._solver_names) > 0
        assert all(isinstance(n, str) for n in self._solver_names)
        self._solvers = []
        for name in self._solver_names:
            solver = _timeout_solver(env, to=self.timeout,
                                     name=name, logic=logic)
            # solver = Solver(env, name=name, logic=logic)
            # _add_timeout_solve_method(solver, timeout)
            assert hasattr(solver, "timeout_solve")
            if pref_vars:
                _set_pref_vars(solver, pref_vars)
            self._solvers.append(solver)
        assert len(self._solvers) > 0
        self._solver_idx = 0
        self._is_timeout = False
        log(f"\tUsing solver: {self._solver_names[self._solver_idx]}",
            self.log_lvl)

    def _segfault_handler(self):
        self._segfault = True

    def __enter__(self):
        # Here we are relying on the fact that `enter` of solvers doesn't do anything.
        assert not hasattr(self, "_prev_handler")
        self._segfault = False
        self._prev_handler = signal(SIGSEGV, self._segfault_handler)
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        for solver in self._solvers:
            solver.exit()
        signal(SIGSEGV, self._prev_handler)
        del self._prev_handler

    @property
    def _c_solver(self):
        return self._solvers[self._solver_idx]

    @property
    def active_solver_name(self) -> str:
        return self._solver_names[self._solver_idx]

    def _next_solver(self) -> None:
        self._solver_idx += 1
        log("\tNo other solvers" if self._solver_idx >= len(self._solvers)
            else f"\tUsing solver: {self._solver_names[self._solver_idx]}",
            self.log_lvl)

    @property
    def assertions(self):
        return self._c_solver.assertions

    def solve(self, assumptions: Iterable[FNode] = None):
        res = None
        assumptions = list(assumptions) if assumptions else None
        while self._solver_idx < len(self._solvers) and res is None:
            try:
                assert self._segfault is False
                res = self._c_solver.timeout_solve(assumptions=assumptions)
            except SolverReturnedUnknownResultError:
                # solver could be in an undefined state, reset assertions.
                self._c_solver.reset_assertions()
                self._is_timeout = True
                res = None
            if self._segfault is True:
                log(f"MultiSolver: {self._solver_names[self._solver_idx]} SEGFAULT;"
                    " proceed by reinstantiatiating solver.",
                    self.log_lvl)
                self._segfault = False
                self._solvers[self._solver_idx] = \
                    _timeout_solver(self.env, to=self.timeout,
                                    name=self._solver_names[self._solver_idx],
                                    logic=self.logic)
                res = None
            if res is None:
                self._next_solver()
        return self._get_solve_result(res)

    def _get_solve_result(self, res: Optional[bool]):
        """Return res if the last solve query was successful;
        Raise exception if some query ended with timeout;
        Return None otherwise"""
        assert res is None or isinstance(res, bool)
        if res is not None:
            assert self._solver_idx < len(self._solvers)
            return res
        if self._solver_idx == len(self._solvers):
            self._solver_idx = 0
            if self._is_timeout:
                self._is_timeout = False
                raise SolverReturnedUnknownResultError()
        return None

    def get_model(self):
        return self._c_solver.get_model()

    def get_values(self, formulae: Iterable[FNode]):
        return self._c_solver.get_values(formulae)

    def push(self, levels: int = 1):
        for s in self._solvers[self._solver_idx:]:
            s.push(levels=levels)

    def pop(self, levels: int = 1):
        for s in self._solvers[self._solver_idx:]:
            s.pop(levels=levels)

    def reset_assertions(self):
        for s in self._solvers:
            s.reset_assertions()
        self._solver_idx = 0
        assert all(len(s.assertions) == 0 for s in self._solvers)

    def add_assertion(self, formula: FNode, named: Optional[str] = None):
        assert formula in self.env.formula_manager.formulae.values()
        for s in self._solvers:
            s.add_assertion(formula, named=named)

    def add_assertions(self, fms: Iterable[FNode]):
        for fm in fms:
            self.add_assertion(fm)

    def get_value(self, formula: FNode):
        assert formula in self.env.formula_manager.formulae.values()
        self._c_solver.get_value(formula)

    def get_py_value(self, formula: FNode):
        assert formula in self.env.formula_manager.formulae.values()
        self._c_solver.get_py_value(formula)

    def get_unsat_core(self):
        self._c_solver.get_unsat_core()

    def get_named_unsat_core(self):
        self._c_solver.get_named_unsat_core()


def _timeout_solver(env: PysmtEnv, to: int, name: str, logic):
    """Instantiate solver `name` with solve timeout `to`."""
    if name == "z3":
        res = Solver(env, name=name, logic=logic,
                     solver_options={"timeout": to * 1000})
        res.timeout_solve = res.solve
        return res

    if name == "msat":
        def _msat_timeout_solve(solver, assumptions: Iterable[FNode] = None):
            start = time.time()
            count = [0]

            def ttest():
                count[0] += 1
                if count[0] == 100:
                    count[0] = 0
                    return int(time.time() - start > to)
                return 0
            mathsat.msat_set_termination_test(solver.msat_env(), ttest)
            return solver.solve(assumptions)

        res = Solver(env, name=name, logic=logic)
        res.timeout_solve = MethodType(_msat_timeout_solve, res)
        return res

    raise Exception("Timeout supported only for MathSAT and Z3.")


# def _add_timeout_solve_method(solver, secs: int) -> None:
#     if isinstance(solver, MathSAT5Solver):
#         def solver_timeout_solve(self, assumptions: Iterable[FNode] = None):
#             start = time.time()
#             count = [0]

#             def ttest():
#                 count[0] += 1
#                 if count[0] == 100:
#                     count[0] = 0
#                     cur = time.time()
#                     return int(cur - start > secs)
#                 return 0
#             mathsat.msat_set_termination_test(solver.msat_env(), ttest)
#             return self.solve(assumptions)
#         timeout_solve = MethodType(solver_timeout_solve, solver)
#     elif isinstance(solver, Z3Solver):
#         solver.z3.set(timeout=secs * 1000)
#         timeout_solve = solver.solve
#     else:
#         raise Exception("Timeout supported only for MathSAT and Z3.")
#     solver.timeout_solve = timeout_solve


def _set_pref_vars(solver, pref_vars: Iterable[FNode]):
    assert pref_vars is not None
    if isinstance(solver, MathSAT5Solver):
        true = solver.env.formula_manager.TRUE()
        for v in pref_vars:
            solver.set_preferred_var(v, val=true)
    elif isinstance(solver, Z3Solver):
        # replace Z3Solver with Z3 Optimize in pysmt object.
        from z3 import Optimize
        from pysmt.solvers.z3 import Z3Converter
        solver.z3 = Optimize()
        solver.converter = Z3Converter(solver.env, solver.z3.ctx)
        for s in pref_vars:
            solver.z3.add_soft(solver.converter.convert(s))
