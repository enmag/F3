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
from pysmt.logics import Logic
from pysmt.exceptions import SolverReturnedUnknownResultError

from solver import get_solvers, Solver
from utils import log


class MultiSolver:
    """Keep multiple solvers synchronised,
    upon failure of one solver try using the following one"""

    def __init__(self, env: PysmtEnv, timeout: int,
                 logic: Logic = None, log_lvl: int = 5,
                 pref_vars=None):
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
        self._solvers = []
        for name in get_solvers():
            solver = Solver(env, name=name, logic=logic)
            _add_timeout_solve_method(solver, timeout)
            if pref_vars:
                _set_pref_vars(solver, pref_vars)
            assert hasattr(solver, "timeout_solve")
            self._solvers.append(solver)

        # self._solvers = [Solver(env, name=name, logic=logic)
        #                  for name in get_solvers()]
        assert len(self._solvers) > 0
        self._solver_idx = 0
        self._is_timeout = False
        log(f"\tUsing solver: {get_solvers()[self._solver_idx]}",
            self.log_lvl)

    def _segfault_handler(self):
        self._segfault = True

    def __enter__(self):
        self._segfault = False
        self._prev_handler = signal(SIGSEGV, self._segfault_handler)
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        for solver in self._solvers:
            solver.exit()
        signal(SIGSEGV, self._prev_handler)
        del self._solvers

    @property
    def _c_solver(self):
        return self._solvers[self._solver_idx]

    @property
    def active_solver_name(self) -> str:
        return get_solvers()[self._solver_idx]

    def _next_solver(self) -> None:
        self._solver_idx += 1
        log("\tNo other solvers" if self._solver_idx >= len(self._solvers)
            else f"\tUsing solver: {get_solvers()[self._solver_idx]}",
            self.log_lvl)

    @property
    def assertions(self):
        return self._c_solver.assertions

    def solve(self, assumptions=None):
        assert assumptions is None or \
            all(s in self.env.formula_manager.formulae.values()
                for s in assumptions)

        res = None
        while self._solver_idx < len(self._solvers) and res is None:
            try:
                # res = solve_with_timeout(self.timeout, self._c_solver,
                #                          assumptions=assumptions)
                assert self._segfault is False
                res = self._c_solver.timeout_solve(assumptions=assumptions)
            except SolverReturnedUnknownResultError:
                # solver could be in an undefined state, reset assertions.
                self._c_solver.reset_assertions()
                self._is_timeout = True
                res = None
            if self._segfault is True:
                self._segfault = False
                new_s = Solver(self.env, name=get_solvers()[self._solver_idx],
                               logic=self.logic)
                self._solvers[self._solver_idx] = new_s
                res = None
            if res is None:
                self._next_solver()
        return self._get_solve_result(res)

    def _get_solve_result(self, res):
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

    def get_values(self, formulae):
        assert all(fm in self.env.formula_manager.formulae.values()
                   for fm in formulae)

        return self._c_solver.get_values(formulae)

    def push(self, levels=1):
        for s in self._solvers[self._solver_idx:]:
            s.push(levels=levels)

    def pop(self, levels=1):
        for s in self._solvers[self._solver_idx:]:
            s.pop(levels=levels)

    def reset_assertions(self):
        for s in self._solvers:
            s.reset_assertions()
        self._solver_idx = 0
        assert all(len(s.assertions) == 0 for s in self._solvers)

    def add_assertion(self, formula, named=None):
        assert formula in self.env.formula_manager.formulae.values()
        for s in self._solvers:
            s.add_assertion(formula, named=named)

    def add_assertions(self, formulae):
        assert all(fm in self.env.formula_manager.formulae.values()
                   for fm in formulae)
        for s in self._solvers:
            s.add_assertions(formulae)

    def get_value(self, formula):
        assert formula in self.env.formula_manager.formulae.values()
        self._c_solver.get_value(formula)

    def get_py_value(self, formula):
        assert formula in self.env.formula_manager.formulae.values()
        self._c_solver.get_py_value(formula)

    def get_unsat_core(self):
        self._c_solver.get_unsat_core()

    def get_named_unsat_core(self):
        self._c_solver.get_named_unsat_core()


def _add_timeout_solve_method(solver, secs: int) -> None:
    if isinstance(solver, MathSAT5Solver):
        def solver_timeout_solve(self, assumptions=None):
            start = time.time()
            count = [0]

            def ttest():
                count[0] += 1
                if count[0] == 100:
                    count[0] = 0
                    cur = time.time()
                    return int(cur - start > secs)
                return 0
            mathsat.msat_set_termination_test(solver.msat_env(), ttest)
            return self.solve(assumptions)
        timeout_solve = MethodType(solver_timeout_solve, solver)
    elif isinstance(solver, Z3Solver):
        solver.z3.set(timeout=secs * 1000)
        timeout_solve = solver.solve
    else:
        raise Exception("Timeout supported only for MathSAT and Z3.")
    solver.timeout_solve = timeout_solve


def _set_pref_vars(solver, pref_vars):
    assert pref_vars is not None
    assert len(pref_vars) > 0
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
