from typing import (FrozenSet, Set, Tuple, Dict, List, Iterable, Iterator,
                    Optional)
from itertools import chain
from random import Random

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
from pysmt.walkers import DagWalker
from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.solvers.solver import Model
from pysmt.solvers.msat import MSatInterpolator
from pysmt.oracles import get_logic
from pysmt.exceptions import PysmtValueError, NoLogicAvailableError

from canonize import Canonizer
from solver import UnsatCoreSolver
from multisolver import MultiSolver
from expr_utils import not_rel, assigns2fnodes, is_atom
from efsolver import efmultisolve


class Implicant(DagWalker):
    """Compute implicant for formula given a model"""
    _TIMEOUT = 5
    _KEEP_PREF = "a"
    _RM_PREF = "_"
    _BOOL_IMPL = True
    _UNSAT_CORES = True
    _ITP_IMPL = False
    _MERGE_INEQS = True
    _MINIMIZE_CORE = True

    @staticmethod
    def get_timeout():
        return Implicant._TIMEOUT

    @staticmethod
    def set_timeout(val: int) -> None:
        assert isinstance(val, int)
        assert val > 0
        Implicant._TIMEOUT = val

    @staticmethod
    def set_use_bool_impl(val: bool) -> None:
        assert isinstance(val, bool)
        Implicant._BOOL_IMPL = val

    @staticmethod
    def get_use_bool_impl() -> bool:
        return Implicant._BOOL_IMPL

    @staticmethod
    def set_use_unsat_cores(val: bool) -> None:
        assert isinstance(val, bool)
        Implicant._UNSAT_CORES = val

    @staticmethod
    def get_use_unsat_cores() -> bool:
        return Implicant._UNSAT_CORES

    @staticmethod
    def set_use_itp_impl(val: bool) -> None:
        assert isinstance(val, bool)
        Implicant._ITP_IMPL = val

    @staticmethod
    def get_use_itp_impl() -> bool:
        return Implicant._ITP_IMPL

    @staticmethod
    def set_merge_ineqs(val: bool) -> None:
        assert isinstance(val, bool)
        Implicant._MERGE_INEQS = val

    @staticmethod
    def get_merge_ineqs() -> bool:
        return Implicant._MERGE_INEQS

    @staticmethod
    def set_minimize_core(val: bool) -> None:
        Implicant._MINIMIZE_CORE = val

    @staticmethod
    def get_minimize_core() -> bool:
        return Implicant._MINIMIZE_CORE

    @staticmethod
    def _keep_pref() -> str:
        return Implicant._KEEP_PREF

    @staticmethod
    def _rm_pref() -> str:
        return Implicant._RM_PREF

    @staticmethod
    def is_itp_supported(env: PysmtEnv, p: FNode) -> bool:
        assert isinstance(env, PysmtEnv)
        assert isinstance(p, FNode)
        assert p in env.formula_manager.formulae.values()
        try:
            logic = get_logic(p, env=env)
        except NoLogicAvailableError:
            return False
        return any(logic <= supp_logic
                   for supp_logic in MSatInterpolator.LOGICS)

    def __init__(self, env: PysmtEnv, cn: Canonizer):
        assert isinstance(env, PysmtEnv)
        assert isinstance(cn, Canonizer)
        super().__init__(env)
        assert cn.env == env
        self.cn = cn
        self.model: Model = None

    def __call__(self, fms: Iterable[FNode],
                 model: Model, assume: Dict[FNode, FNode]) -> FrozenSet[FNode]:
        return self.get_impl(fms, model, assume)

    def get_impl(self, res: Iterable[FNode], model: Model,
                 assume: Dict[FNode, FNode]) -> FrozenSet[FNode]:
        assert Implicant.get_use_bool_impl() or Implicant.get_use_unsat_cores()
        if __debug__:
            from itertools import tee
            res, _orig = tee(res, 2)
            _orig = list(_orig)
            assert all(isinstance(fm, FNode) for fm in _orig)
            assert all(fm in self.env.formula_manager.formulae.values()
                       for fm in _orig)
            assert all(model.get_value(fm).is_true() for fm in _orig)
            assert all(self.cn(fm) == fm for fm in _orig)
            assert all(self.cn(k) == k for k in assume)
        if Implicant.get_use_bool_impl():
            res = self.bool_impl(res, model, assume)
            if Implicant.get_merge_ineqs():
                res = self.merge_ineqs(res)
        if Implicant.get_use_unsat_cores():
            res = self.ucore_impl(res, model, assume)
            if not Implicant.get_use_bool_impl() and \
               Implicant.get_merge_ineqs():
                res = self.merge_ineqs(res)
        if Implicant.get_use_itp_impl():
            res = self.itp_impl(res, model, assume)
            if not Implicant.get_use_bool_impl() and \
               Implicant.get_merge_ineqs():
                res = self.merge_ineqs(res)

        assert isinstance(res, (set, frozenset))
        assert all(model.get_value(p).is_true() for p in res)
        if __debug__:
            from solver import Solver
            mgr = self.env.formula_manager
            # Valid(res -> _orig)
            with Solver(self.env) as _solver:
                _solver.add_assertions(res)
                _solver.add_assertions(assigns2fnodes(self.env, assume))
                _solver.add_assertion(mgr.Not(mgr.And(_orig)))
                assert _solver.solve() is False
        return frozenset(res)

    def merge_ineqs(self, fms: Iterable[FNode]) -> Set[FNode]:
        fms = set(fms)
        assert all(isinstance(fm, FNode) for fm in fms)
        assert all(fm in self.env.formula_manager.formulae.values()
                   for fm in fms)
        assert all(self.cn(fm) == fm for fm in fms)
        if __debug__:
            _dbg_fms = frozenset(fms)
        mgr = self.env.formula_manager
        get_type = self.env.stc.get_type
        res = set()
        i_1 = mgr.Int(1)
        i_2 = mgr.Int(2)
        with MultiSolver(self.env, Implicant.get_timeout(),
                         solver_names=["msat"]) as solver:
            solver.add_assertions(fms)
            while fms:
                curr = fms.pop()
                rhs = None
                assert self.cn(curr) == curr
                assert not curr.is_and()
                try:
                    if curr.is_le():
                        # (a <= b & a >= b) <-> a = b
                        rhs = self.cn(mgr.GE(curr.arg(0), curr.arg(1)))
                        fms.remove(rhs)
                        curr = self.cn(mgr.Equals(curr.arg(0), curr.arg(1)))
                    elif curr.is_lt() and get_type(curr.arg(0)).is_int_type():
                        # (a < b & a > b - 2) <-> a = b - 1
                        assert get_type(curr.arg(1)).is_int_type()
                        rhs = self.cn(mgr.GT(curr.arg(0),
                                             mgr.Minus(curr.arg(1), i_2)))
                        fms.remove(rhs)
                        curr = self.cn(mgr.Equals(curr.arg(0),
                                                  mgr.Minus(curr.arg(1), i_1)))
                except KeyError:
                    # >=/> not in set, try using SMT-solver, otherwise keep <=/<.
                    assert rhs is not None
                    if rhs is not None:
                        solver.push()
                        solver.add_assertion(mgr.Not(rhs))
                        try:
                            sat = solver.solve()
                        except SolverReturnedUnknownResultError:
                            sat = None
                            solver.add_assertions(fms)
                            solver.add_assertions(res)
                            solver.add_assertion(curr)
                            solver.push()
                        solver.pop()
                        if sat is False:
                            if curr.is_le():
                                curr = self.cn(mgr.Equals(curr.arg(0), curr.arg(1)))
                            else:
                                assert curr.is_lt() and get_type(curr.arg(0)).is_int_type()
                                curr = self.cn(mgr.Equals(curr.arg(0),
                                                          mgr.Minus(curr.arg(1), i_1)))
                if curr.is_false():
                    if __debug__:
                        from solver import Solver
                        with Solver(self.env) as _solver:
                            _solver.add_assertions(_dbg_fms)
                            assert _solver.solve() is False
                    return frozenset([curr])
                if not curr.is_true():
                    res.add(curr)
                    fms.discard(curr)
        if __debug__:
            from solver import Solver
            # Valid(res <-> formulae)
            with Solver(self.env) as _solver:
                _solver.add_assertion(mgr.Not(mgr.Iff(mgr.And(res),
                                                      mgr.And(_dbg_fms))))
                assert _solver.solve() is False
        assert isinstance(res, set)
        assert all(isinstance(p, FNode) for p in res)
        assert all(not p.is_true() for p in res)
        assert all(not p.is_false() for p in res)
        return res

    def bool_impl(self, fms: Iterable[FNode], model: Model,
                  assume: Dict[FNode, FNode]) -> FrozenSet[FNode]:
        """Compute boolean implicant"""
        return self.walk(fms, model, assume)

    def ucore_impl(self, fms: Iterable[FNode], model: Model,
                   assume: Dict[FNode, FNode]) -> FrozenSet[FNode]:
        """Compute unsat-core implicant"""
        assert hasattr(model, "get_value")
        if __debug__:
            from itertools import tee
            fms, _fms = tee(fms, 2)
            _fms = list(_fms)
            assert all(isinstance(fm, FNode) for fm in _fms)
            assert all(model.get_value(fm).is_true() for fm in _fms)
            del _fms
        assert isinstance(assume, dict)
        assert all(isinstance(k, FNode) for k in assume)
        assert all(k in self.env.formula_manager.formulae.values()
                   for k in assume)
        assert all(isinstance(v, FNode) for v in assume.values())
        assert all(v in self.env.formula_manager.formulae.values()
                   for v in assume.values())
        return self.rm_redundant_conjs(self._gen_conjuncts(fms, model),
                                       assume)

    def itp_impl(self, fms: Iterable[FNode], model: Model,
                 assume: Dict[FNode, FNode]) -> FrozenSet[FNode]:
        """Compute implicant using interpolants"""
        assert hasattr(model, "get_value")
        if __debug__:
            from itertools import tee
            fms, _fms = tee(fms, 2)
            _fms = list(_fms)
            assert all(isinstance(fm, FNode) for fm in _fms)
            assert all(model.get_value(fm).is_true() for fm in _fms)
        assert isinstance(assume, dict)
        assert all(isinstance(k, FNode) for k in assume)
        assert all(k in self.env.formula_manager.formulae.values()
                   for k in assume)
        assert all(isinstance(v, FNode) for v in assume.values())
        assert all(v in self.env.formula_manager.formulae.values()
                   for v in assume.values())
        mgr = self.env.formula_manager
        get_free_vars = self.env.fvo.get_free_variables
        # interpolation supported only on some theories.
        itp_fms = []
        unsupp_fms = []
        # Here we assume that the interpolator supports the combination of the theories.
        for fm in fms:
            if Implicant.is_itp_supported(self.env, fm):
                itp_fms.append(fm)
            else:
                unsupp_fms.append(fm)
        n_fms = mgr.Not(mgr.And(itp_fms))
        lhs = mgr.And(chain(assigns2fnodes(self.env, {s: model.get_value(s)
                                                      for s in get_free_vars(n_fms)}),
                            assigns2fnodes(self.env, assume)))
        with self.env.factory.Interpolator() as interp:
            itp = interp.binary_interpolant(lhs, n_fms)
        stack = [self.cn(itp)]
        res = set(self.bool_impl(unsupp_fms, model, assume))
        while stack:
            curr = stack.pop()
            if curr.is_and():
                stack.extend(curr.args())
            if is_atom(curr):
                res.add(curr)
            else:
                res.update(self.bool_impl([curr], model, assume))

        if __debug__:
            from solver import Solver
            assert all(isinstance(pred, FNode) for pred in res)
            assert all(self.cn(pred) == pred for pred in res)
            assert all(is_atom(pred) for pred in res)
            assert all(model.get_value(pred).is_true() for pred in res)
            # Valid(res & assume -> _fms)
            with Solver(self.env) as _solver:
                _solver.add_assertions(res)
                _solver.add_assertions(assigns2fnodes(self.env, assume))
                _solver.add_assertion(mgr.Not(mgr.And(_fms)))
                assert _solver.solve() is False
        return frozenset(res)

    def _gen_conjuncts(self, fms: Iterable[FNode], model):
        mgr = self.env.formula_manager
        get_atms = self.env.ao.get_atoms
        for a in chain.from_iterable(get_atms(fm) for fm in fms):
            assert isinstance(a, FNode)
            assert a in mgr.formulae.values()
            if model.get_value(a).is_false():
                if not (a.is_equals() or a.is_le() or a.is_lt()):
                    a = mgr.Not(a)
                elif a.is_le():
                    a = mgr.GT(a.arg(0), a.arg(1))
                elif a.is_lt():
                    a = mgr.GE(a.arg(0), a.arg(1))
                else:
                    _gt = mgr.GT(a.arg(0), a.arg(1))
                    a = _gt if model.get_value(_gt).is_true() \
                        else mgr.LT(a.arg(0), a.arg(1))
                a = self.cn(a)
            assert a == self.cn(a)
            yield a

    def rm_redundant_conjs(self, fms: Iterable[FNode],
                           assume: Dict[FNode, FNode]) -> FrozenSet[FNode]:
        """Compute unsat-core of purely conjunctive formula"""
        mgr = self.env.formula_manager
        fms = list(fms)
        if len(fms) == 0:
            return frozenset()
        assert all(isinstance(fm, FNode) for fm in fms)
        assert all(fm in mgr.formulae.values() for fm in fms)
        assert all(fm.is_literal() or fm.is_bool_constant() or
                   fm.is_le() or fm.is_lt() or fm.is_equals()
                   for fm in fms)
        assert all(self.cn(fm) == fm for fm in fms)
        assert isinstance(assume, dict)
        assert all(isinstance(k, FNode) for k in assume)
        assert all(k in self.env.formula_manager.formulae.values()
                   for k in assume)
        assert all(isinstance(v, FNode) for v in assume.values())
        assert all(v in self.env.formula_manager.formulae.values()
                   for v in assume.values())
        cores = {f"{Implicant._keep_pref()}{num}": fm
                 for num, fm in enumerate(fms)}
        cores[f"{Implicant._rm_pref()}nf"] = mgr.Not(mgr.And(fms))
        cores = self._fixpoint_core(cores,
                                    list(assigns2fnodes(self.env, assume)))
        assert all(k.startswith(f"{Implicant._rm_pref()}") or
                   v == self.cn(v) for k, v in cores.items())
        assert all(not c.is_true() for c in cores.values())
        if __debug__:
            from solver import Solver
            with Solver(self.env) as _solver:
                for c in cores.values():
                    _solver.add_assertion(c)
                if assume is not None:
                    _solver.add_assertions(list(assigns2fnodes(self.env, assume)))
                assert _solver.solve() is False

        assert all(k.startswith(f"{Implicant._rm_pref()}") or
                   k.startswith(f"{Implicant._keep_pref()}")
                   for k in cores)
        res = frozenset(p for k, p in cores.items()
                        if k.startswith(f"{Implicant._keep_pref()}"))
        assert all(p == self.cn(p) for p in res)
        assert all(p.is_literal() or p.is_le() or p.is_lt() or
                   p.is_equals() or p.is_bool_constant()
                   for p in res)
        if __debug__:
            # consistency check: we still have an implicant.
            from solver import Solver
            with Solver(env=self.env) as _solver:
                # Valid(res & assume -> formula)
                _solver.add_assertions(res)
                _solver.add_assertions(assigns2fnodes(self.env, assume))
                _solver.add_assertion(mgr.Not(mgr.And(fms)))
                assert _solver.solve() is False
        return res

    def rm_deadlocks(self, reg: Iterable[FNode],
                     trans: Iterable[FNode]) -> Iterator[FNode]:
        """Return formulae whose negation contains deadlocks of reg w.r.t trans"""
        mgr = self.env.formula_manager
        get_free_vars = self.env.fvo.get_free_variables
        if __debug__:
            from itertools import tee
            _trans, trans = tee(trans, 2)
            _trans = mgr.And(_trans)
        # Interpolation supported only on linear theories.
        # Consider subset of linear conjuncts in reg and trans: weaker formulae.
        # Here we assume that the interpolator supports the combination of the theories.
        reg = mgr.And(filter(lambda p: Implicant.is_itp_supported(self.env, p),
                             reg))
        trans = mgr.And(filter(lambda p: Implicant.is_itp_supported(self.env, p),
                               trans))
        if trans.is_true():
            return
        n_trans = mgr.Not(trans)
        e_symbs = get_free_vars(reg)
        f_symbs = get_free_vars(trans) - e_symbs
        with self.env.factory.Interpolator() as interp:
            cex, _ = efmultisolve(self.env, e_symbs, f_symbs,
                                  mgr.And(reg, n_trans))
            while cex:
                assert isinstance(cex, dict)
                assert all(isinstance(k, FNode) for k in cex)
                assert all(k in mgr.get_all_symbols() for k in cex)
                assert all(isinstance(v, FNode) for v in cex.values())
                assert all(v in mgr.formulae.values() for v in cex.values())
                assert all(v.is_constant() for v in cex.values())
                assert self.env.simplifier.simplify(
                    self.env.substituter.substitute(reg, cex)).is_true()
                assert all(Implicant.is_itp_supported(self.env, p)
                           for p in assigns2fnodes(self.env, cex))

                cex = mgr.And(assigns2fnodes(self.env, cex))
                if __debug__:
                    from solver import Solver
                    with Solver(self.env) as _solver:
                        _solver.add_assertion(cex)
                        _solver.add_assertion(_trans)
                        assert _solver.solve() is False
                ref = interp.binary_interpolant(trans, cex)
                assert ref is not None
                assert isinstance(ref, FNode)
                assert get_free_vars(ref) <= e_symbs
                if __debug__:
                    from solver import Solver
                    # ref -> !cex
                    with Solver(env=self.env) as _solver:
                        _solver.add_assertion(ref)
                        _solver.add_assertion(cex)
                        assert _solver.solve() is False
                    # trans -> ref
                    with Solver(env=self.env) as _solver:
                        _solver.add_assertion(_trans)
                        _solver.add_assertion(mgr.Not(ref))
                        assert _solver.solve() is False
                yield ref
                if ref.is_false():
                    return
                reg = mgr.And(reg, ref)
                cex, _ = efmultisolve(self.env, e_symbs, f_symbs,
                                      mgr.And(reg, n_trans))

    def walk(self, fms: Iterable[FNode], model: Model,
             assume: Dict[FNode, FNode]) -> FrozenSet[FNode]:
        if __debug__:
            from itertools import tee
            fms, _fms = tee(fms, 2)
            _fms = list(_fms)
            assert all(fm in self.env.formula_manager.formulae.values()
                       for fm in _fms)
            assert all(model.get_value(fm).is_true() for fm in _fms)
        assert hasattr(model, "get_value")
        assert isinstance(assume, dict)
        assert all(isinstance(k, FNode) for k in assume)
        assert all(k in self.env.formula_manager.formulae.values()
                   for k in assume)
        assert all(isinstance(v, FNode) for v in assume.values())
        assert all(v in self.env.formula_manager.formulae.values()
                   for v in assume.values())
        assert all(model.get_value(k) == model.get_value(v)
                   for k, v in assume.items())
        self.memoization.clear()
        self.model = model
        simpl = self.env.simplifier.simplify
        subst = self.env.substituter.substitute
        res = set()
        for fm in fms:
            res.update(super().walk(self.cn(simpl(subst(fm, assume))))[1])
        self.model = None
        res = frozenset(res)
        if __debug__:
            from expr_utils import is_atom
            from solver import Solver
            mgr = self.env.formula_manager
            assert all(isinstance(pred, FNode) for pred in res)
            assert all(self.cn(pred) == pred for pred in res)
            assert all(is_atom(pred) for pred in res)
            assert all(model.get_value(pred).is_true() for pred in res)
            # Valid(res & assume -> fms)
            with Solver(self.env) as _solver:
                _solver.add_assertions(res)
                _solver.add_assertions(assigns2fnodes(self.env, assume))
                _solver.add_assertion(mgr.Not(mgr.And(_fms)))
                assert _solver.solve() is False
        return res

    def _fixpoint_core(self, cores: Dict[str, FNode],
                       assume: List[FNode]) -> Dict[str, FNode]:
        """Compute unsat-cores of previous core until fixpoint"""
        assert isinstance(cores, dict)
        assert all(isinstance(k, str) for k in cores)
        assert all(k.startswith(f"{Implicant._rm_pref()}") or
                   k.startswith(f"{Implicant._keep_pref()}")
                   for k in cores)
        assert all(isinstance(v, FNode) for v in cores.values())
        assert all(v in self.env.formula_manager.formulae.values()
                   for v in cores.values())
        assert isinstance(assume, list)
        assert all(isinstance(pred, FNode) for pred in assume)
        assert all(pred in self.env.formula_manager.formulae.values()
                   for pred in assume)
        rand = Random(10)
        old_cores = None
        with UnsatCoreSolver(self.env, unsat_cores_mode="named") as solver:
            while old_cores != cores:
                old_cores = cores
                solver.reset_assertions()
                name_core_lst = list(cores.items())
                rand.shuffle(name_core_lst)
                for k, c in name_core_lst:
                    solver.add_assertion(c, named=k)
                sat = solver.solve(assume)
                assert sat is False
                cores = solver.get_named_unsat_core()
                if __debug__:
                    from solver import Solver
                    with Solver(self.env) as _solver:
                        for c in cores.values():
                            _solver.add_assertion(c)
                        if assume is not None:
                            _solver.add_assertions(assume)
                        assert _solver.solve() is False
            if Implicant.get_minimize_core():
                k = self._find_redundant_ineq(cores, assume)
                if k is not None:
                    assert k in cores
                    cores.pop(k)
        return cores

    def _find_redundant_ineq(self, cores: Dict[str, FNode],
                             assume: List[FNode]) -> Optional[str]:
        """Possibly expensive check, consider only subset of predicates.
        Find ineq in cores that can be safely removed."""
        mgr = self.env.formula_manager
        assertions = list(assume) if assume else []
        ineqs = []
        k_ineqs = []
        for k, v in cores.items():
            if k.startswith(Implicant._keep_pref()) and \
               (v.is_lt() or v.is_le()):
                ineqs.append(v)
                k_ineqs.append(k)
            else:
                assertions.append(v)
        with MultiSolver(self.env,
                         timeout=Implicant.get_timeout(),
                         solver_names=["msat"]) as solver:

            solver.add_assertions(assertions)
            while len(ineqs) > 0:
                assert len(ineqs) == len(k_ineqs)
                v = ineqs[-1]
                ineqs[-1] = mgr.Not(v)
                try:
                    assert len(solver.assertions) == len(assertions)
                    if solver.solve(ineqs) is False:
                        assert cores[k_ineqs[-1]] == v
                        return k_ineqs[-1]
                except SolverReturnedUnknownResultError:
                    solver.reset_assertions()
                    solver.add_assertions(assertions)
                ineqs.pop()
                k_ineqs.pop()
                solver.add_assertion(v)
                assertions.append(v)
        return None

    def _get_children(self, fm: FNode):
        """Override parent method: avoid visit of theory nodes in bool-impl"""
        return [] if (fm.is_symbol() or fm.is_theory_relation() or
                      fm.is_bool_constant()) else super()._get_children(fm)

    def _rank(self, impls: FrozenSet[FNode]) -> tuple:
        """Used to heuristically rank implicants, the smaller the better"""
        assert isinstance(impls, frozenset)
        assert all(isinstance(impl, FNode) for impl in impls)
        assert all(impl in self.env.formula_manager.formulae.values()
                   for impl in impls)
        symbs = frozenset(chain.from_iterable(
            self.env.fvo.get_free_variables(impl) for impl in impls))
        assert all(isinstance(s, FNode) for s in symbs)
        assert all(s.is_symbol() for s in symbs)
        n_symbs = len(symbs)
        n_inf_state_symbs = len(list(s for s in symbs
                                     if not s.symbol_type().is_bool_type()))
        n_ineqs = len(list(impl for impl in impls
                           if impl.is_le() or impl.is_lt()))
        return (n_inf_state_symbs, n_symbs, n_ineqs, len(impls))

    # Walker methods to compute boolean implicant.
    def walk_bool_constant(self, _, **__) -> Tuple[FrozenSet[FNode],
                                                   FrozenSet[FNode]]:
        return frozenset([]), frozenset([])

    def walk_symbol(self, fm, **_) -> Tuple[FrozenSet[FNode], FrozenSet[FNode]]:
        assert fm.is_symbol()
        assert fm.symbol_type().is_bool_type()
        return frozenset([self.env.formula_manager.Not(fm)]), frozenset([fm])

    def walk_lt(self, fm, **_) -> Tuple[FrozenSet[FNode], FrozenSet[FNode]]:
        assert self.cn(fm) == fm
        return frozenset([self.cn(not_rel(self.env, fm))]), frozenset([fm])

    def walk_le(self, fm, **_) -> Tuple[FrozenSet[FNode], FrozenSet[FNode]]:
        assert self.cn(fm) == fm
        return frozenset([self.cn(not_rel(self.env, fm))]), frozenset([fm])

    def walk_equals(self, fm, **_) -> Tuple[FrozenSet[FNode], FrozenSet[FNode]]:
        assert self.cn(fm) == fm
        n_fm = self.env.formula_manager.LT(fm.arg(0), fm.arg(1))
        if self.model.get_value(n_fm).is_false():
            n_fm = self.env.formula_manager.LT(fm.arg(1), fm.arg(0))
        return frozenset([self.cn(n_fm)]), frozenset([fm])

    def walk_and(self, fm, args) -> Tuple[FrozenSet[FNode], FrozenSet[FNode]]:
        assert len(args) >= 2
        assert all(len(arg) == 2 for arg in args)
        # pairs: <formula, neg_impl>
        pairs = list(zip(fm.args(), [arg[0] for arg in args]))
        fm, neg = pairs.pop()
        # find child assigned to false with min rank.
        while pairs and self.model.get_value(fm).is_true():
            fm, neg = pairs.pop()
        min_rank = self._rank(neg)
        for fm, curr in pairs:
            c_rank = self._rank(curr)
            if c_rank < min_rank and self.model.get_value(fm).is_false():
                neg, min_rank = curr, c_rank
        return neg, frozenset.union(*(arg[1] for arg in args))

    def walk_or(self, fm, args) -> Tuple[FrozenSet[FNode], FrozenSet[FNode]]:
        assert len(args) >= 2
        assert len(args) == len(fm.args())
        assert all(len(arg) == 2 for arg in args)
        pairs = list(zip(fm.args(), [arg[1] for arg in args]))
        fm, pos = pairs.pop()
        # find child assigned to true with min rank.
        while pairs and self.model.get_value(fm).is_false():
            fm, pos = pairs.pop()
        min_rank = self._rank(pos)
        for fm, curr in pairs:
            c_rank = self._rank(curr)
            if c_rank < min_rank and self.model.get_value(fm).is_true():
                pos, min_rank = curr, c_rank
        return frozenset.union(*(arg[0] for arg in args)), pos

    def walk_not(self, _, args) -> Tuple[FrozenSet[FNode], FrozenSet[FNode]]:
        assert len(args) == 1
        assert all(len(arg) == 2 for arg in args)
        # invert polarity.
        return args[0][1], args[0][0]

    def walk_iff(self, fm, args) -> Tuple[FrozenSet[FNode], FrozenSet[FNode]]:
        assert len(args) == 2
        assert all(len(arg) == 2 for arg in args)
        lhs_impl, rhs_impl = args
        if self.model.get_value(fm.arg(0)).is_true():
            neg = lhs_impl[1] | rhs_impl[0]
            pos = lhs_impl[1] | rhs_impl[1]
        else:
            neg = lhs_impl[0] | rhs_impl[1]
            pos = lhs_impl[0] | rhs_impl[0]
        return neg, pos

    def walk_implies(self, fm, args) -> Tuple[FrozenSet[FNode],
                                              FrozenSet[FNode]]:
        assert len(args) == 2
        assert all(len(arg) == 2 for arg in args)
        lhs, rhs = args
        lhs_t = self.model.get_value(fm.arg(0)).is_false()
        rhs_t = self.model.get_value(fm.arg(1)).is_true()
        if lhs_t and rhs_t:
            pos = rhs[1] if self._rank(rhs[1]) < self._rank(lhs[0]) else lhs[0]
        elif lhs_t:
            pos = lhs[0]
        else:
            pos = rhs[1]
        return lhs[1] | rhs[0], pos
