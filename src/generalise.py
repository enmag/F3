from typing import Tuple, List, Set, FrozenSet, Dict, Iterable, Optional, Union
from itertools import chain
from random import Random

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
from pysmt.exceptions import SolverReturnedUnknownResultError

from canonize import Canonizer
from expr_at_time import ExprAtTime
from multisolver import MultiSolver
from solver import UnsatCoreSolver
from utils import assign2fnodes


class Generaliser:
    """Find formula implicant from model"""

    _LOG_LVL = 3
    _TIMEOUT = 5
    _KEEP_PREF = "a"
    _DISC_PREF = "_a"
    _FM_PREF = "_nf"

    _BOOL_IMPL = True
    _UNSAT_CORES = True
    _MERGE_INEQS = True
    _MINIMAL_CORE = True

    @staticmethod
    def set_use_bool_impl(val: bool) -> None:
        assert isinstance(val, bool)
        Generaliser._BOOL_IMPL = val

    @staticmethod
    def get_use_bool_impl() -> bool:
        return Generaliser._BOOL_IMPL

    @staticmethod
    def set_use_unsat_cores(val: bool) -> None:
        assert isinstance(val, bool)
        Generaliser._UNSAT_CORES = val

    @staticmethod
    def get_use_unsat_cores() -> bool:
        return Generaliser._UNSAT_CORES

    @staticmethod
    def set_merge_ineqs(val: bool) -> None:
        assert isinstance(val, bool)
        Generaliser._MERGE_INEQS = val

    @staticmethod
    def get_merge_ineqs() -> bool:
        return Generaliser._MERGE_INEQS

    @staticmethod
    def set_minimal_core(val: bool) -> None:
        Generaliser._MINIMAL_CORE = val

    @staticmethod
    def get_minimal_core() -> bool:
        return Generaliser._MINIMAL_CORE

    @staticmethod
    def set_timeout(val: int) -> None:
        assert isinstance(val, int)
        assert val > 0
        Generaliser._TIMEOUT = val

    @staticmethod
    def get_timeout() -> int:
        return Generaliser._TIMEOUT


    def __init__(self, env: PysmtEnv, cn: Canonizer, totime: ExprAtTime):
        assert isinstance(env, PysmtEnv)
        assert isinstance(cn, Canonizer)
        assert isinstance(totime, ExprAtTime)
        self.env = env
        self.cn = cn
        self.totime = totime

    def subst(self, f: FNode, s: Dict[FNode, FNode]) -> FNode:
        assert isinstance(f, FNode)
        assert f in self.env.formula_manager.formulae.values()
        assert isinstance(s, dict)
        assert all(isinstance(k, FNode) for k in s)
        assert all(isinstance(v, FNode) for v in s.values())
        assert all(k in self.env.formula_manager.formulae.values() for k in s)
        assert all(v in self.env.formula_manager.formulae.values() for v in s.values())

        return self.env.substituter.substitute(f, s)

    def simpl(self, f: FNode) -> FNode:
        assert isinstance(f, FNode)
        assert f in self.env.formula_manager.formulae.values()

        return self.env.simplifier.simplify(f)

    def curr_next_preds(self, preds: Union[FrozenSet[FNode], List[FNode]],
                        first: int, last: int,
                        model) -> Tuple[List[FrozenSet[FNode]],
                                        List[FrozenSet[FNode]]]:
        assert isinstance(preds, (frozenset, list))
        assert all(isinstance(p, FNode) for p in preds)
        assert all(p in self.env.formula_manager.formulae.values()
                   for p in preds)
        assert all(not p.is_true() for p in preds)
        assert all(not p.is_false() for p in preds)
        assert all(p.is_literal() or p.is_lt() or p.is_le() or p.is_equals()
                   for p in preds)
        assert 0 <= first < last
        assert isinstance(first, int)
        assert isinstance(last, int)
        assert hasattr(model, "get_value")
        mgr = self.env.formula_manager
        get_free_vars = self.env.fvo.walk
        curr_only: List[Set[FNode]] = [set() for _ in range(first, last + 1)]
        curr_next: List[Set[FNode]] = [set() for _ in range(first, last)]
        preds = list(preds)
        while preds:
            p = preds.pop()
            if p.is_and():
                preds.extend(p.args()[1:])
                p = p.arg(0)
            assert len(self.env.ao.get_atoms(p)) == 1
            is_next = ExprAtTime.collect_times(mgr, p)
            assert len(get_free_vars(p)) >= 1, p.serialze()
            assert len(is_next) in {1, 2}
            assert min(is_next) >= first
            assert max(is_next) <= last
            assert min(is_next) == max(is_next) or \
                min(is_next) + 1 == max(is_next)
            c_time = min(is_next)
            idx = c_time - first
            is_next = len(is_next) == 2
            # map `symb = 0` to next assignment on previous step.
            if p.is_equals() and len(get_free_vars(p)) == 1 and \
               c_time > first:
                c_time -= 1
                idx -= 1
                is_next = True
            p = self.cn(self.totime(p, -c_time - 1))
            assert len(ExprAtTime.collect_times(mgr, p)) == 0
            assert self.cn(p) == p
            if not is_next:
                curr_only[idx].add(p)
            else:
                curr_next[idx].add(p)
        assert all(len(self.env.ao.get_atoms(p)) == 1
                   for preds in curr_only
                   for p in preds)
        assert all(len(self.env.ao.get_atoms(p)) == 1
                   for preds in curr_next
                   for p in preds)
        return ([frozenset(preds) for preds in curr_only],
                [frozenset(preds) for preds in curr_next])

    def generalise_path(self, formula: Iterable[FNode], model,
                        timed_symbs: List[FrozenSet[FNode]],
                        first: int, last: int,
                        assume: Optional[Dict[FNode, FNode]] = None) -> FrozenSet[FNode]:
        assert isinstance(formula, Iterable)
        assert hasattr(model, "get_value")
        assert isinstance(timed_symbs, list)
        assert all(isinstance(symbs, frozenset) for symbs in timed_symbs)
        assert all(isinstance(s, FNode)
                   for symbs in timed_symbs for s in symbs)
        assert all(s.is_symbol()
                   for symbs in timed_symbs for s in symbs)
        assert all(s in self.env.formula_manager.get_all_symbols()
                   for symbs in timed_symbs for s in symbs)
        assert isinstance(first, int)
        assert isinstance(last, int)
        assert 0 <= first < last
        assert all(min(ExprAtTime.collect_times(self.env.formula_manager, s)) >= first
                   for symbs in timed_symbs for s in symbs)
        assert all(max(ExprAtTime.collect_times(self.env.formula_manager, s)) <= last
                   for symbs in timed_symbs for s in symbs)
        mgr = self.env.formula_manager
        get_free_vars = self.env.fvo.walk
        symbs = frozenset(chain.from_iterable(timed_symbs))
        # discard formulae that contain no interesting symbol.
        formula = [f for f in formula if len(get_free_vars(f) & symbs) > 0]
        assert all(isinstance(f, FNode) for f in formula)
        assert all(f in self.env.formula_manager.formulae.values() for f in formula)

        # substitute prefix predicates with their truth assignment
        substs = {**(assume if assume is not None else {}),
                  **{atm: model.get_value(atm)
                     for f in formula for atm in self.env.ao.get_atoms(f)
                     if self._should_substitute(atm, first, symbs)},
                  # **{s: model.get_value(s)
                  #    for s in fm_symbs - symbs}
                  }
        # substitute preds with time < lback with their truth assignment.
        res = set(self.simpl(self.subst(f, substs)) for f in formula)
        res.discard(mgr.TRUE())
        assert all(get_free_vars(f) <= symbs for f in res)
        assert all(last >= t
                   for fm in res
                   for t in ExprAtTime.collect_times(mgr, fm))
        assert all(len(ExprAtTime.collect_times(mgr, a)) == 0 or
                   min(ExprAtTime.collect_times(mgr, a)) >= first
                   for fm in res for a in self.env.ao.get_atoms(fm))
        assert all(len(ExprAtTime.collect_times(mgr, a)) == 0 or
                   min(ExprAtTime.collect_times(mgr, a)) <= last
                   for fm in res for a in self.env.ao.get_atoms(fm))

        return self.generalise(res, model, symbs, assume=assume)

    def merge_ineqs(self, formulae: Union[FrozenSet[FNode],
                                          Set[FNode]]) -> FrozenSet[FNode]:
        assert isinstance(formulae, (set, frozenset))
        assert all(isinstance(pred, FNode) for pred in formulae)

        mgr = self.env.formula_manager
        get_type = self.env.stc.get_type
        res = set()
        fms = set(formulae)
        while fms:
            curr = fms.pop()
            assert self.cn(curr) == curr
            assert not curr.is_and()
            if curr.is_le():
                # (a <= b & a >= b) <-> a = b
                neg_curr = self.cn(mgr.GE(curr.arg(0), curr.arg(1)))
                try:
                    fms.remove(neg_curr)
                    res.add(self.cn(mgr.Equals(curr.arg(0), curr.arg(1))))
                except KeyError:
                    # neg_curr not in set.
                    res.add(curr)
            elif curr.is_lt() and get_type(curr.arg(0)).is_int_type():
                # (a < b & a > b - 2) <-> a = b - 1
                assert get_type(curr.arg(1)).is_int_type()
                neg_curr = self.cn(mgr.GT(curr.arg(0), mgr.Minus(curr.arg(1),
                                                                 mgr.Int(2))))
                try:
                    fms.remove(neg_curr)
                    res.add(self.cn(mgr.Equals(curr.arg(0),
                                               mgr.Minus(curr.arg(1),
                                                         mgr.Int(1)))))
                except KeyError:
                    # neg_curr not in set.
                    res.add(curr)
            else:
                res.add(curr)

        if __debug__:
            from solver import Solver
            # res is sat
            with Solver(env=self.env) as _solver:
                _solver.add_assertions(res)
                assert _solver.solve() is True
            # Valid(res <-> formulae)
            with Solver(env=self.env) as _solver:
                _solver.add_assertion(mgr.Not(mgr.Iff(mgr.And(res),
                                                      mgr.And(formulae))))
                assert _solver.solve() is False
        assert isinstance(res, set)
        assert all(isinstance(pred, FNode) for pred in res)
        return frozenset(res)

    def __call__(self, res: Union[FrozenSet[FNode], Set[FNode]], model,
                 symbs: FrozenSet[FNode],
                 assume: Optional[Dict[FNode, FNode]] = None) -> FrozenSet[FNode]:
        return self.generalise(res, model, symbs, assume)

    def generalise(self, res: Union[FrozenSet[FNode], Set[FNode]], model,
                   symbs: FrozenSet[FNode],
                   assume: Optional[Dict[FNode, FNode]] = None) -> FrozenSet[FNode]:
        assert isinstance(res, (frozenset, set))
        assert all(isinstance(p, FNode) for p in res)
        assert all(p in self.env.formula_manager.formulae.values()
                   for p in res)
        assert all(self.env.stc.get_type(p).is_bool_type() for p in res)
        assert hasattr(model, "get_value")
        assert isinstance(symbs, frozenset)
        assert all(isinstance(s, FNode) for s in symbs)
        assert all(s in self.env.formula_manager.get_all_symbols()
                   for s in symbs)
        assert assume is None or isinstance(assume, dict)
        assert assume is None or all(isinstance(k, FNode) for k in assume)
        assert assume is None or all(isinstance(v, FNode)
                                     for v in assume.values())
        # compute implicant of res.
        if Generaliser.get_use_bool_impl():
            res = self.bool_impl(res, model)
            assert all(len(self.env.ao.get_atoms(p)) == 1
                       for p in res)

        if Generaliser.get_use_unsat_cores():
            res = self.unsat_core_impl(res, model, symbs, assume=assume)

        # merge inequalities a <= b & b <= a into a = b
        if Generaliser.get_merge_ineqs():
            res = self.merge_ineqs(res)

        assert isinstance(res, (set, frozenset))
        assert all(isinstance(pred, FNode) for pred in res)
        return frozenset(res)

    def bool_impl(self, fm: Iterable[FNode], model) -> FrozenSet[FNode]:
        assert isinstance(fm, (list, frozenset, set))
        assert hasattr(model, "get_value")
        assert all(model.get_value(f).is_true() for f in fm)

        mgr = self.env.formula_manager
        cache = {mgr.TRUE(): [None, frozenset()],
                 mgr.FALSE(): [frozenset(), None]}
        res: Set[FNode] = set()
        for f in fm:
            self._bool_impl_rec(f, model, True, cache)
            res.update(cache[f][int(True)])
        assert all(self.cn(it) == it for it in res)

        if __debug__:
            # res -> fm
            from solver import Solver
            with Solver(env=self.env) as _solver:
                for c in res:
                    _solver.add_assertion(c)
                _solver.add_assertion(mgr.Not(mgr.And(fm)))
                assert _solver.solve() is False
            # res is satisfiable
            with Solver(env=self.env) as _solver:
                for pred in res:
                    _solver.add_assertion(pred)
                assert _solver.solve() is True
            assert model.get_value(mgr.And(res)).is_true()

        return frozenset(res)

    def unsat_core_impl(self, formulae: Union[FrozenSet[FNode], Set[FNode]],
                        model, symbs: FrozenSet[FNode],
                        assume: Optional[Dict[FNode, FNode]] = None) -> FrozenSet[FNode]:
        assert isinstance(formulae, (frozenset, set))
        assert hasattr(model, "get_value")
        assert all(isinstance(f, FNode) for f in formulae)
        assert isinstance(symbs, frozenset)
        assert all(model.get_value(formula).is_true() for formula in formulae)
        assert assume is None or isinstance(assume, dict)
        assert assume is None or all(isinstance(k, FNode) for k in assume)
        assert assume is None or all(isinstance(v, FNode)
                                     for v in assume.values())
        assert assume is None or \
            all(k in self.env.formula_manager.formulae.values()
                for k in assume)
        assert assume is None or \
            all(v in self.env.formula_manager.formulae.values()
                for v in assume.values())
        mgr = self.env.formula_manager
        assume = list(assign2fnodes(self.env, assume)) if assume else []

        # canonize formula atoms.
        f_atoms = frozenset(self.cn(a)
                            for f in formulae for a in self.env.ao.get_atoms(f))

        assert all(isinstance(a, FNode) for a in f_atoms)
        assert all(a == self.cn(a) for a in f_atoms)

        with UnsatCoreSolver(env=self.env,
                             unsat_cores_mode="named") as solver:
            assert len(solver.assertions) == 0
            # ! (& formulae)
            solver.add_assertion(mgr.Or(mgr.Not(f) for f in formulae),
                                 named="_nf")
            # counter is used to create new names for cores
            for counter, a in enumerate(f_atoms):
                assert len(self.env.fvo.walk(a) & symbs) == 0 or \
                    self.env.fvo.walk(a) <= symbs
                name = "a{}" if self.env.fvo.walk(a) <= symbs else "_a{}"
                name = name.format(counter)

                assert model.get_value(a).is_true() or \
                    model.get_value(a).is_false()

                if model.get_value(a).is_false():
                    if not a.is_equals() and not a.is_le() and \
                       not a.is_lt():
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
                solver.add_assertion(a, named=name)

            counter = len(f_atoms)
            sat = solver.solve(assume)
            assert sat is False
            cores = solver.get_named_unsat_core()
        if __debug__:
            from solver import Solver
            with Solver(env=self.env) as _solver:
                assert len(_solver.assertions) == 0
                for c in cores.values():
                    _solver.add_assertion(c)
                assert _solver.solve() is False

        # here we try to refine the unsat-cores
        # we compute the unsat cores of the unsat cores until fixpoint.
        # we shuffle the order of the cores to increase the probability
        # that the solver will return a different unsat core.
        # We use a fixed seed for reproducibility.
        assert all(k.startswith("_nf") or v == self.cn(v)
                   for k, v in cores.items())

        cores = Generaliser._fixpoint_unsat_cores(self.env, cores,
                                                  Random(10), assume,
                                                  key="a")
        assert all(k.startswith("_nf") or v == self.cn(v)
                   for k, v in cores.items())
        assert all(not c.is_true() for c in cores.values())
        if __debug__:
            from solver import Solver
            with Solver(env=self.env) as _solver:
                assert len(_solver.assertions) == 0
                for c in cores.values():
                    _solver.add_assertion(c)
                if assume is not None:
                    _solver.add_assertions(assume)
                assert _solver.solve() is False

        res = frozenset(c for k, c in cores.items()
                        if k.startswith("a"))

        assert all(pred == self.cn(pred) for pred in res)

        if __debug__:
            # consistency check: we still have an underapproximation.
            from solver import Solver
            assert all(k.startswith("_nf") or k.startswith("a") or
                       k.startswith("_a") for k in cores)
            lhs = [c for k, c in cores.items()
                   if k.startswith("a") or k.startswith("_a")]
            if assume is not None:
                lhs.extend(assume)
            with Solver(env=self.env) as _solver:
                # Valid(lhs -> formula) => Unsat(lhs & !formula)
                n_formula = mgr.Not(mgr.And(formulae))
                _solver.add_assertion(mgr.And(lhs))
                _solver.add_assertion(n_formula)
                assert _solver.solve() is False

            # res is satisfiable
            with Solver(env=self.env) as _solver:
                for pred in res:
                    _solver.add_assertion(pred)
                if assume is not None:
                    _solver.add_assertions(assume)
                assert _solver.solve() is True

        return res

    def _should_substitute(self, atm: FNode, idx: int,
                           keep_symbs: frozenset) -> bool:
        assert isinstance(atm, FNode)
        assert isinstance(idx, int)
        assert idx >= 0
        if not self.env.fvo.get_free_variables(atm) <= keep_symbs:
            return True
        atm_times = ExprAtTime.collect_times(self.env.formula_manager, atm)
        if not atm_times:
            return False
        # max_time = max(atm_times)
        min_time = min(atm_times)
        return min_time < idx
        # return max_time < idx or (max_time == idx and len(atm_times) == 2)

    def _bool_impl_rec(self, fm: FNode, model, pol: bool,
                       cache: dict) -> None:
        assert isinstance(fm, FNode)
        assert isinstance(pol, bool)
        assert isinstance(cache, dict)
        assert not pol or model.get_value(fm).is_true()
        assert pol or model.get_value(fm).is_false()
        assert not fm.is_true() or pol
        assert not fm.is_false() or not pol

        res = cache.get(fm)
        if res and res[pol] is not None:
            return

        assert not fm.is_true()
        assert not fm.is_false()

        mgr = self.env.formula_manager
        if res is None:
            res = [None, None]

        # compute res[pol] as curr_impl
        curr_impl = None
        # negation
        if fm.is_not():
            self._bool_impl_rec(fm.arg(0), model, not pol, cache)
            curr_impl = cache[fm.arg(0)][not pol]
        # positive AND or negative OR
        elif (fm.is_and() and pol) or (fm.is_or() and not pol):
            # must consider all children
            curr_impl = set()
            for child in fm.args():
                assert not pol or model.get_value(child).is_true()
                assert pol or model.get_value(child).is_false()
                self._bool_impl_rec(child, model, pol, cache)
                curr_impl.update(cache[child][pol])
            curr_impl = frozenset(curr_impl)
        # negative AND or positive OR
        elif (fm.is_and() and not pol) or (fm.is_or() and pol):
            # consider shortest child.
            assert not pol or any(model.get_value(c).is_true()
                                  for c in fm.args())
            assert pol or any(model.get_value(c).is_false() for c in fm.args())
            assert curr_impl is None
            curr_rank = None
            for child in filter(lambda c: (pol and model.get_value(c).is_true()) or
                                (not pol and model.get_value(c).is_false()),
                                fm.args()):
                self._bool_impl_rec(child, model, pol, cache)
                c_impl = cache[child][pol]
                new_rank = _rank_implicant(self.env, c_impl)
                if curr_rank is None or new_rank < curr_rank:
                    curr_rank = new_rank
                    curr_impl = c_impl
        # positive implies
        elif pol and fm.is_implies():
            lhs = fm.arg(0)
            rhs = fm.arg(1)
            assert (model.get_value(lhs).is_true() and
                    model.get_value(rhs).is_true()) or \
                model.get_value(lhs).is_false()
            if model.get_value(lhs).is_false():
                self._bool_impl_rec(lhs, model, False, cache)
                curr_impl = cache[lhs][False]
                if model.get_value(rhs).is_true():
                    self._bool_impl_rec(rhs, model, True, cache)
                    rhs = cache[rhs][True]
                    curr_rank = _rank_implicant(self.env, curr_impl)
                    rhs_rank = _rank_implicant(self.env, rhs)
                    curr_impl = curr_impl if curr_rank <= rhs_rank \
                        else rhs
            else:
                self._bool_impl_rec(lhs, model, True, cache)
                lhs = cache[lhs][True]
                self._bool_impl_rec(rhs, model, True, cache)
                rhs = cache[rhs][True]
                curr_impl = lhs | rhs
        # negative implies
        elif not pol and fm.is_implies():
            lhs = fm.arg(0)
            rhs = fm.arg(1)
            assert model.get_value(lhs).is_true() and \
                model.get_value(rhs).is_false()
            self._bool_impl_rec(lhs, model, True, cache)
            lhs = cache[lhs][True]
            self._bool_impl_rec(rhs, model, False, cache)
            rhs = cache[rhs][False]
            curr_impl = lhs | rhs
        # positive iff
        elif pol and fm.is_iff():
            lhs = fm.arg(0)
            rhs = fm.arg(1)
            assert (model.get_value(lhs).is_true() and
                    model.get_value(rhs).is_true()) or \
                (model.get_value(lhs).is_false() and
                 model.get_value(rhs).is_false())
            if model.get_value(lhs).is_true():
                self._bool_impl_rec(lhs, model, True, cache)
                lhs = cache[lhs][True]
                self._bool_impl_rec(rhs, model, True, cache)
                rhs = cache[rhs][True]
            else:
                self._bool_impl_rec(lhs, model, False, cache)
                lhs = cache[lhs][False]
                self._bool_impl_rec(rhs, model, False, cache)
                rhs = cache[rhs][False]
            curr_impl = lhs | rhs
        # negative iff
        elif not pol and fm.is_iff():
            lhs = fm.arg(0)
            rhs = fm.arg(1)
            assert (model.get_value(lhs).is_true() and
                    model.get_value(rhs).is_false()) or \
                (model.get_value(lhs).is_false() and
                 model.get_value(rhs).is_true())
            if model.get_value(lhs).is_true():
                self._bool_impl_rec(lhs, model, True, cache)
                lhs = cache[lhs][True]
                self._bool_impl_rec(rhs, model, False, cache)
                rhs = cache[rhs][False]
            else:
                self._bool_impl_rec(lhs, model, False, cache)
                lhs = cache[lhs][False]
                self._bool_impl_rec(rhs, model, True, cache)
                rhs = cache[rhs][True]
            curr_impl = lhs | rhs
        # positive atom
        elif pol and (fm.is_lt() or fm.is_le() or fm.is_equals() or
                      fm.is_literal()):
            curr_impl = frozenset([self.cn(fm)])
        # negative <
        elif not pol and fm.is_lt():
            curr_impl = frozenset([self.cn(mgr.GE(fm.arg(0),
                                                  fm.arg(1)))])
        # negative <=
        elif not pol and fm.is_le():
            curr_impl = frozenset([self.cn(mgr.GT(fm.arg(0),
                                                  fm.arg(1)))])
        # negative literal
        elif not pol and fm.is_literal():
            curr_impl = frozenset([self.cn(mgr.Not(fm))])
        # negative equality
        elif not pol and fm.is_equals():
            gt = mgr.GT(fm.arg(0), fm.arg(1))
            if model.get_value(gt).is_true():
                curr_impl = frozenset([self.cn(gt)])
            else:
                lt = mgr.LT(fm.arg(0), fm.arg(1))
                curr_impl = frozenset([self.cn(lt)])
        else:
            assert False
        # End of method
        assert isinstance(curr_impl, frozenset)
        # assert len(curr_impl) > 0
        assert int(pol) in {0, 1}
        assert len(res) == 2
        res[int(pol)] = curr_impl
        cache[fm] = res

    @staticmethod
    def _fixpoint_unsat_cores(env: PysmtEnv, cores: Dict[str, FNode],
                              rand: Random, assume: List[FNode],
                              key: str) -> Dict[str, FNode]:
        assert isinstance(env, PysmtEnv)
        assert isinstance(cores, dict)
        assert all(isinstance(k, str) for k in cores)
        assert all(isinstance(v, FNode) for v in cores.values())
        assert all(v in env.formula_manager.formulae.values()
                   for v in cores.values())
        assert isinstance(rand, Random)
        assert isinstance(assume, list)
        assert all(isinstance(pred, FNode) for pred in assume)
        assert all(pred in env.formula_manager.formulae.values()
                   for pred in assume)
        assert isinstance(key, str)
        old_cores = None
        with UnsatCoreSolver(env=env, unsat_cores_mode="named") as solver:
            while old_cores != cores:
                old_cores = cores
                solver.reset_assertions()
                assert len(solver.assertions) == 0, solver.assertions
                name_core_lst = list(cores.items())
                rand.shuffle(name_core_lst)
                for k, c in name_core_lst:
                    solver.add_assertion(c, named=k)
                sat = solver.solve(assume)
                assert sat is False
                cores = solver.get_named_unsat_core()
                if __debug__:
                    from solver import Solver
                    assert env == solver.env
                    with Solver(env=env) as _solver:
                        assert len(_solver.assertions) == 0
                        for c in cores.values():
                            _solver.add_assertion(c)
                        if assume is not None:
                            _solver.add_assertions(assume)
                        assert _solver.solve() is False

            if Generaliser.get_minimal_core() and cores == old_cores:
                k = _core_find_redundant_ineq(env, cores, key=key)
                if k is not None:
                    assert k in cores
                    cores.pop(k)
        # assert not Generaliser.get_minimal_core() or \
        #     _core_find_redundant_ineq(env, cores, key=key) is None
        return cores


def _rank_implicant(env: PysmtEnv, impls: FrozenSet[FNode]) -> tuple:
    """Used to heuristically rank implicants, the smaller the better"""
    assert isinstance(env, PysmtEnv)
    assert isinstance(impls, frozenset)
    assert all(isinstance(impl, FNode) for impl in impls)
    assert all(impl in env.formula_manager.formulae.values()
               for impl in impls)
    symbs = frozenset(chain.from_iterable(env.fvo.walk(impl)
                                          for impl in impls))
    assert all(isinstance(s, FNode) for s in symbs)
    assert all(s.is_symbol() for s in symbs)
    n_symbs = len(symbs)
    n_inf_state_symbs = len(list(s for s in symbs
                                 if not s.symbol_type().is_bool_type()))
    n_ineqs = len(list(impl for impl in impls if impl.is_le() or impl.is_lt()))
    return (n_inf_state_symbs, n_symbs, n_ineqs, len(impls))


def _core_find_redundant_ineq(env: PysmtEnv, cores: Dict[str, FNode],
                              key: str):
    """Possibly expensive check, consider only subset of predicates.
    Find ineq in cores with id starting with key that can be safely removed."""
    with MultiSolver(env=env, timeout=Generaliser.get_timeout()) as solver:
        for curr_k, curr_v in cores.items():
            if curr_k.startswith(key) and (curr_v.is_lt() or curr_v.is_le()):
                solver.reset_assertions()
                for other_k, other_v in cores.items():
                    if curr_k != other_k:
                        solver.add_assertion(other_v)
                try:
                    sat = solver.solve()
                except SolverReturnedUnknownResultError:
                    sat = None
                if sat is False:
                    return curr_k
    return None
