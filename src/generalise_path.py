from typing import Tuple, List, Set, Union, FrozenSet
from itertools import chain
from random import Random

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode

from canonize import Canonizer
from expr_at_time import ExprAtTime
from solver import UnsatCoreSolver


class Generaliser:
    """Find formula implicant from model"""

    _LOG_LVL = 3
    _KEEP_PREF = "a"
    _DISC_PREF = "_a"
    _FM_PREF = "_nf"

    _BOOL_IMPL = True
    _UNSAT_CORES = True
    _MERGE_INEQS = True

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

    def __init__(self, env: PysmtEnv, cn: Canonizer, totime: ExprAtTime):
        assert isinstance(env, PysmtEnv)
        assert isinstance(cn, Canonizer)
        assert isinstance(totime, ExprAtTime)
        self.env = env
        self.mgr = env.formula_manager
        self.cn = cn
        self.totime = totime

    def subst(self, f: FNode, s: dict):
        assert isinstance(f, FNode)
        assert f in self.mgr.formulae.values()
        assert isinstance(s, dict)
        assert all(isinstance(k, FNode) for k in s.keys())
        assert all(isinstance(v, FNode) for v in s.values())
        assert all(k in self.mgr.formulae.values() for k in s.keys())
        assert all(v in self.mgr.formulae.values() for v in s.values())

        return self.env.substituter.substitute(f, s)

    def simpl(self, f: FNode) -> FNode:
        assert isinstance(f, FNode)
        assert f in self.mgr.formulae.values()

        return self.env.simplifier.simplify(f)

    def curr_next_preds(self, preds: frozenset,
                        first: int, last: int) -> Tuple[List[frozenset],
                                                        List[frozenset]]:
        assert isinstance(preds, frozenset)
        assert all(isinstance(p, FNode) for p in preds)
        assert all(p in self.mgr.formulae.values() for p in preds)
        assert all(not p.is_true() for p in preds), preds
        assert all(not p.is_false() for p in preds), preds
        assert all(p.is_literal() or p.is_lt() or p.is_le() or p.is_equals()
                   for p in preds), preds
        assert 0 <= first < last
        assert isinstance(first, int)
        assert isinstance(last, int)
        curr_only: List[Set[FNode]] = [set() for _ in range(first, last + 1)]
        curr_next: List[Set[FNode]] = [set() for _ in range(first, last)]

        preds = list(preds)
        while preds:
            p = preds.pop()
            if p.is_and():
                preds.extend(p.args()[1:])
                p = p.arg(0)
            assert len(p.get_atoms()) == 1, p.serialize()
            is_next = ExprAtTime.collect_times(self.mgr, p)
            assert len(p.get_free_variables()) >= 1, p.serialze()
            assert len(is_next) in {1, 2}, p.serialize()
            assert min(is_next) >= first
            assert max(is_next) <= last
            assert min(is_next) == max(is_next) or \
                min(is_next) + 1 == max(is_next), p.serialize()
            c_time = min(is_next)
            idx = c_time - first
            is_next = len(is_next) == 2
            # map `symb = 0` to next assignment on previous step.
            if p.is_equals() and len(p.get_free_variables()) == 1 and \
               c_time > first:
                c_time -= 1
                idx -= 1
                is_next = True
            p = self.cn(self.totime(p, -c_time - 1))
            assert len(ExprAtTime.collect_times(self.mgr, p)) == 0
            assert self.cn(p) == p, p.serialize()
            if not is_next:
                curr_only[idx].add(p)
            else:
                curr_next[idx].add(p)
        assert all(len(p.get_atoms()) == 1
                   for preds in curr_only
                   for p in preds)
        assert all(len(p.get_atoms()) == 1
                   for preds in curr_next
                   for p in preds)

        return ([frozenset(preds) for preds in curr_only],
                [frozenset(preds) for preds in curr_next])

    def __call__(self, formula: list, model, timed_symbs: list,
                 first: int, last: int, assume: dict = {}) -> frozenset:
        return self.generalise(formula, model, timed_symbs, first, last,
                               assume)

    def generalise(self, formula: list, model, timed_symbs: list,
                   first: int, last: int, assume: dict = {}) -> frozenset:
        assert isinstance(formula, list)
        assert all(isinstance(f, FNode) for f in formula)
        assert all(f in self.mgr.formulae.values() for f in formula)
        assert hasattr(model, "get_value")
        assert isinstance(timed_symbs, list)
        assert all(isinstance(symbs, frozenset) for symbs in timed_symbs)
        assert all(isinstance(s, FNode)
                   for symbs in timed_symbs for s in symbs)
        assert all(s.is_symbol()
                   for symbs in timed_symbs for s in symbs)
        assert all(s in self.mgr.get_all_symbols()
                   for symbs in timed_symbs for s in symbs)
        assert isinstance(first, int)
        assert isinstance(last, int)
        assert 0 <= first < last
        assert all(min(ExprAtTime.collect_times(self.mgr, s)) >= first
                   for symbs in timed_symbs for s in symbs)
        assert all(max(ExprAtTime.collect_times(self.mgr, s)) <= last
                   for symbs in timed_symbs for s in symbs)

        symbs = frozenset(chain.from_iterable(timed_symbs))
        fm_symbs = frozenset(chain.from_iterable(f.get_free_variables()
                                                 for f in formula))
        fm_atms = frozenset(atm for f in formula for atm in f.get_atoms())
        # substitute prefix predicates with their truth assignment
        substs = {**assume,
                  **{atm: model.get_value(atm)
                     for atm in fm_atms
                     if self._should_substitute(atm, first, fm_symbs - symbs)},
                  # **{s: model.get_value(s)
                  #    for s in fm_symbs - symbs}
                  }
        del fm_atms

        # substitute preds with time < lback with their truth assignment.
        res = frozenset(filter(lambda f: not f.is_true(),
                               (self.simpl(self.subst(f, substs))
                                for f in formula)))
        assert all(f.get_free_variables() <= symbs for f in res)
        # compute boolean implicant of resulting formula.
        if Generaliser.get_use_bool_impl():
            res = self.bool_impl(res, model)

        if Generaliser.get_use_unsat_cores():
            res = self.unsat_core_impl(res, model, symbs, first, last)

        # merge inequalities a <= b & b <= a into a = b
        if Generaliser.get_merge_ineqs():
            new_res = set()
            if __debug__:
                prev_res = frozenset(r for r in res)
            res = set(res)
            while res:
                curr = res.pop()
                assert self.cn(curr) == curr
                if not curr.is_le():
                    new_res.add(curr)
                else:
                    neg_curr = self.cn(self.mgr.GE(curr.arg(0), curr.arg(1)))
                    try:
                        res.remove(neg_curr)
                        eq = self.cn(self.mgr.Equals(curr.arg(0), curr.arg(1)))
                        new_res.add(eq)
                    except KeyError:
                        # neg_curr not in set.
                        new_res.add(curr)
            res = frozenset(new_res)
            if __debug__:
                from solver import Solver
                # res is sat
                with Solver(env=self.env) as solver:
                    for constr in res:
                        solver.add_assertion(constr)
                    sat = solver.solve()
                    assert sat is True
                # check res <-> prev_res
                constr = self.mgr.Iff(self.mgr.And(res), self.mgr.And(prev_res))
                with Solver(env=self.env) as solver:
                    solver.add_assertion(self.mgr.Not(constr))
                    sat = solver.solve()
                    assert sat is False

        return res

    def bool_impl(self, fm: Union[list, frozenset, set],
                  model) -> FrozenSet[FNode]:
        assert isinstance(fm, (list, frozenset, set))
        assert hasattr(model, "get_value")

        cache = {self.mgr.TRUE(): [None, frozenset()],
                 self.mgr.FALSE(): [frozenset(), None]}
        res = set()
        for f in fm:
            self._bool_impl_rec(f, model, True, cache)
            res.update(cache[f][int(True)])
        assert all(self.cn(it) == it for it in res)
        res = frozenset(res)
        if __debug__:
            # res -> fm
            from solver import Solver
            with Solver(env=self.env) as solver:
                for c in res:
                    solver.add_assertion(c)
                solver.add_assertion(self.mgr.Not(self.mgr.And(fm)))
                sat = solver.solve()
                assert sat is False
            # res is satisfiable
            with Solver(env=self.env) as _solver:
                for pred in res:
                    _solver.add_assertion(pred)
                sat = _solver.solve()
                assert sat is True
            assert model.get_value(self.mgr.And(res)).is_true()

        return res

    def unsat_core_impl(self, formulae: frozenset, model, symbs: frozenset,
                        first: int, last: int) -> FrozenSet[FNode]:
        assert isinstance(formulae, frozenset)
        assert hasattr(model, "get_value")
        assert all(isinstance(f, FNode) for f in formulae)
        assert isinstance(symbs, frozenset)
        assert isinstance(first, int)
        assert isinstance(last, int)
        assert 0 <= first
        assert first < last
        assert all(last >= t
                   for formula in formulae
                   for t in ExprAtTime.collect_times(self.mgr, formula))
        assert all(min(ExprAtTime.collect_times(self.mgr, s)) >= first
                   for s in symbs)
        assert all(min(ExprAtTime.collect_times(self.mgr, s)) <= last
                   for s in symbs)
        assert all(model.get_value(formula).is_true() for formula in formulae)

        # normalise formula atoms.
        f_atoms = frozenset(self.cn(a)
                            for f in formulae for a in f.get_atoms())

        assert all(isinstance(a, FNode) for a in f_atoms)
        assert all(a == self.cn(a) for a in f_atoms)

        with UnsatCoreSolver(env=self.env,
                             unsat_cores_mode="named") as solver:
            assert len(solver.assertions) == 0
            # ! (& formulae)
            solver.add_assertion(self.cn(self.mgr.Or(self.mgr.Not(f)
                                                     for f in formulae)),
                                 named="_nf")
            # counter is used to create new names for cores
            for counter, a in enumerate(f_atoms):
                assert len(a.get_free_variables() & symbs) == 0 or \
                    a.get_free_variables() <= symbs, (a.serialize(), symbs)
                name = "a{}" if a.get_free_variables() <= symbs else "_a{}"
                name = name.format(counter)

                assert len(ExprAtTime.collect_times(self.mgr, a)) == 0 or \
                    min(ExprAtTime.collect_times(self.mgr, a)) >= first
                assert len(ExprAtTime.collect_times(self.mgr, a)) == 0 or \
                    max(ExprAtTime.collect_times(self.mgr, a)) <= last
                assert model.get_value(a).is_true() or \
                    model.get_value(a).is_false()

                if model.get_value(a).is_false():
                    if not a.is_equals() and not a.is_le() and \
                       not a.is_lt():
                        a = self.mgr.Not(a)
                    elif a.is_le():
                        a = self.mgr.GT(a.arg(0), a.arg(1))
                    elif a.is_lt():
                        a = self.mgr.GE(a.arg(0), a.arg(1))
                    else:
                        # TODO: here we could rewrite the != as either > or <.
                        # Not clear the pros and cons.
                        # a = self.i_mgr.Not(a)
                        _gt = self.mgr.GT(a.arg(0), a.arg(1))
                        a = _gt if model.get_value(_gt).is_true() \
                            else self.mgr.LT(a.arg(0), a.arg(1))
                    a = self.cn(a)

                assert a == self.cn(a), a.serialize()
                solver.add_assertion(a, named=name)

            counter = len(f_atoms)
            sat = solver.solve()
            assert sat is False
            cores = solver.get_named_unsat_core()
            if __debug__:
                from solver import Solver
                with Solver(env=self.env) as _solver:
                    assert len(_solver.assertions) == 0
                    for c in cores.values():
                        _solver.add_assertion(c)
                    sat = _solver.solve()
                    assert sat is False, _solver.assertions

            # TODO: What about computing a minimal unsat-core?
            # here we try to refine the unsat-cores
            # we compute the unsat cores of the unsat cores until fixpoint.
            # we shuffle the order of the cores to increase the probability
            # that the solver will return a different unsat core.
            # We use a fixed seed for reproducibility.
            # symbs_eqs = [dict() for _ in range(max_time - first + 1)]
            assert all(v == self.cn(v) for v in cores.values())

            cores = Generaliser._fixpoint_unsat_cores(solver, cores,
                                                      Random(10))

            assert all(v == self.cn(v) for v in cores.values())
            assert all(not c.is_true() for c in cores.values())
            if __debug__:
                with Solver(env=self.env) as _solver:
                    assert len(_solver.assertions) == 0
                    for c in cores.values():
                        _solver.add_assertion(c)
                    sat = _solver.solve()
                    assert sat is False, _solver.assertions

            res = frozenset(c for k, c in cores.items()
                            if k.startswith("a"))

            assert all(pred == self.cn(pred) for pred in res)

            if __debug__:
                # consistency check: we still have an underapproximation.
                from solver import Solver
                assert all(k.startswith("_nf") or k.startswith("a") or
                           k.startswith("_a") for k in cores.keys())
                lhs = [c for k, c in cores.items()
                       if k.startswith("a") or k.startswith("_a")]
                with Solver(env=self.env) as _solver:
                    # Valid(lhs -> formula) => Unsat(lhs & !formula)
                    n_formula = self.mgr.Not(self.mgr.And(formulae))
                    _solver.add_assertion(self.mgr.And(lhs))
                    _solver.add_assertion(n_formula)
                    assert _solver.solve() is False

                # res is satisfiable
                with Solver(env=self.env) as _solver:
                    for pred in res:
                        _solver.add_assertion(pred)
                    sat = _solver.solve()
                    assert sat is True

        return res

    def _should_substitute(self, atm: FNode, idx: int,
                           remove_symbs: frozenset) -> bool:
        assert isinstance(atm, FNode)
        assert isinstance(idx, int)
        assert idx >= 0
        if len(atm.get_free_variables() & remove_symbs) > 0:
            return True
        atm_times = ExprAtTime.collect_times(self.mgr, atm)
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
            assert not pol or any(model.get_value(c).is_true() for c in fm.args())
            assert pol or any(model.get_value(c).is_false() for c in fm.args())
            assert curr_impl is None
            curr_rank = None
            for child in filter(lambda c: (pol and model.get_value(c).is_true()) or
                                (not pol and model.get_value(c).is_false()),
                                fm.args()):
                self._bool_impl_rec(child, model, pol, cache)
                c_impl = cache[child][pol]
                new_rank = _rank_implicant(c_impl)
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
                    curr_rank = _rank_implicant(curr_impl)
                    rhs_rank = _rank_implicant(rhs)
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
            curr_impl = frozenset([self.cn(self.mgr.GE(fm.arg(0),
                                                       fm.arg(1)))])
        # negative <=
        elif not pol and fm.is_le():
            curr_impl = frozenset([self.cn(self.mgr.GT(fm.arg(0),
                                                       fm.arg(1)))])
        # negative literal
        elif not pol and fm.is_literal():
            curr_impl = frozenset([self.cn(self.mgr.Not(fm))])
        # negative equality
        elif not pol and fm.is_equals():
            gt = self.mgr.GT(fm.arg(0), fm.arg(1))
            if model.get_value(gt).is_true():
                curr_impl = frozenset([self.cn(gt)])
            else:
                lt = self.mgr.LT(fm.arg(0), fm.arg(1))
                curr_impl = frozenset([self.cn(lt)])
        else:
            assert False, fm.serialize()
        # End of method
        assert isinstance(curr_impl, frozenset)
        # assert len(curr_impl) > 0, fm.serialize()
        assert int(pol) in {0, 1}
        assert len(res) == 2
        res[int(pol)] = curr_impl
        cache[fm] = res

    @staticmethod
    def _fixpoint_unsat_cores(solver, cores, rand) -> dict:
        old_cores = None
        while old_cores != cores:
            old_cores = cores
            solver.reset_assertions()
            assert len(solver.assertions) == 0, solver.assertions
            name_core_lst = list(cores.items())
            rand.shuffle(name_core_lst)
            for k, c in name_core_lst:
                solver.add_assertion(c, named=k)
            sat = solver.solve()
            assert sat is False, (solver.assertions, solver.get_model())
            cores = solver.get_named_unsat_core()
            if __debug__:
                from solver import Solver
                assert isinstance(solver.environment, PysmtEnv)
                with Solver(env=solver.environment) as _solver:
                    assert len(_solver.assertions) == 0
                    for c in cores.values():
                        _solver.add_assertion(c)
                    sat = _solver.solve()
                    assert sat is False, _solver.assertions
        return cores


def _rank_implicant(impls: frozenset) -> tuple:
    """Used to heuristically rank implicants, the smaller the better"""
    assert isinstance(impls, frozenset)
    assert all(isinstance(impl, FNode) for impl in impls)
    symbs = frozenset(chain.from_iterable(impl.get_free_variables()
                                          for impl in impls))
    assert all(isinstance(s, FNode) for s in symbs)
    assert all(s.is_symbol() for s in symbs)
    n_symbs = len(symbs)
    n_inf_state_symbs = len(list(s for s in symbs
                                 if not s.symbol_type().is_bool_type()))
    return (n_inf_state_symbs, n_symbs, len(impls))

# def _rank_implicant(impls: frozenset) -> tuple:
#     """Used to heuristically rank implicants, the smaller the better"""
#     assert isinstance(impls, frozenset)
#     assert all(isinstance(impl, FNode) for impl in impls)
#     return len(impls)
