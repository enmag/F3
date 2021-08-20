from __future__ import annotations
from typing import Optional, Tuple, List, FrozenSet, Dict, Iterator
from enum import IntEnum, unique
from itertools import chain

from pysmt.environment import Environment as PysmtEnv
from pysmt.typing import PySMTType
from pysmt.fnode import FNode
from pysmt.exceptions import SolverReturnedUnknownResultError

from rankfun import RankFun
from multisolver import MultiSolver
from efsolver import efesolve
from utils import symb_is_curr, symb_to_next, to_next, new_enum
from canonize import Canonizer
from expr_at_time import ExprAtTime
from generalise import Generaliser

_TIMEOUT = 20


def set_timeout(val: int) -> None:
    assert isinstance(val, int)
    global _TIMEOUT
    _TIMEOUT = val


def get_timeout() -> int:
    global _TIMEOUT
    return _TIMEOUT


@unique
class TransType(IntEnum):
    GT_0 = 0
    EQ_0 = 1
    STUTTER = 2
    RANKED = 3


class Location():
    """Represents a location of an hint:
    - region: condition ensured by entering transitions.
    - assumption: condition that must be ensured by environment.
    - ranking function: bounds number of repetitions of ranking transition.
    - stuttering transition: self-loop on location with constant ranking function.
    - ranked transition: self-loop on location with decreasing ranking function.
    - progress: <idx, prog0, prog1> index of next location.
    """
    # TODO allow list of stutterT, rankT and progressT. Each should satisfy the hypotheses.
    # at the moment a similar result can be achieved by providing multiple Hints.

    def __init__(self, env: PysmtEnv, region: FNode,
                 assume: Optional[FNode] = None,
                 stutterT: Optional[FNode] = None,
                 rankT: Optional[FNode] = None,
                 rf: Optional[RankFun] = None,
                 progressT: Optional[Dict[int, Tuple[FNode, FNode]]] = None):
        assert isinstance(env, PysmtEnv)
        assert isinstance(region, FNode)
        assert region in env.formula_manager.formulae.values()
        assert assume is None or isinstance(assume, FNode)
        assert assume is None or assume in env.formula_manager.formulae.values()
        assert stutterT is None or isinstance(stutterT, FNode)
        assert stutterT is None or stutterT in env.formula_manager.formulae.values()
        assert rankT is None or isinstance(rankT, FNode)
        assert rankT is None or rankT in env.formula_manager.formulae.values()
        assert rf is None or isinstance(rf, RankFun)
        assert rf is None or rf.env == env

        mgr = env.formula_manager
        self.env = env
        self.region = region
        self.assume = assume if assume is not None else mgr.TRUE()
        self.stutterT = stutterT if stutterT else mgr.FALSE()
        self.rankT = rankT if rankT else mgr.FALSE()
        self.rf = rf
        self.progressT: Dict[int, Tuple[FNode, FNode]] = progressT \
            if progressT is not None else {}

    @property
    def ranked_region(self) -> FNode:
        mgr = self.env.formula_manager
        if self.rf is None:
            return mgr.FALSE()
        return mgr.And(self.region, self.rf.is_ranked)

    @property
    def minrf_region(self) -> FNode:
        if self.rf is None:
            return self.region
        mgr = self.env.formula_manager
        return mgr.And(self.region, mgr.Not(self.rf.is_ranked))

    @property
    def dsts(self) -> FrozenSet[int]:
        assert isinstance(self.progressT, dict)
        return frozenset(self.progressT.keys())

    def set_rank(self, trans: FNode, rf: RankFun) -> None:
        assert isinstance(trans, FNode)
        assert trans in self.env.formula_manager.formulae.values()
        assert isinstance(rf, RankFun)
        assert rf.env == self.env
        assert rf.expr in self.env.formula_manager.formulae.values()
        self._rankT = trans
        self._rf = rf

    def progress_gt_0(self, dst: int) -> Optional[FNode]:
        """Return progress transition such that rf' > 0"""
        el = self.progressT.get(dst)
        return el[TransType.GT_0] if el else None

    def progress_eq_0(self, dst: int) -> Optional[FNode]:
        """Return progress transition such that rf' = 0"""
        el = self.progressT.get(dst)
        return el[TransType.EQ_0] if el else None

    def set_progress(self, dst: int,
                     gt_0: Optional[FNode] = None,
                     eq_0: Optional[FNode] = None) -> None:
        assert isinstance(dst, int)
        assert dst >= 0
        assert gt_0 is not None or eq_0 is not None
        assert gt_0 is None or isinstance(gt_0, FNode)
        assert gt_0 is None or \
            gt_0 in self.env.formula_manager.formulae.values()
        assert eq_0 is None or isinstance(eq_0, FNode)
        assert eq_0 is None or \
            eq_0 in self.env.formula_manager.formulae.values()
        assert TransType.GT_0 == 0
        assert TransType.EQ_0 == 1
        self.progressT[dst] = (gt_0, eq_0)

    def get_trans(self, idx: int, lvals: List[FNode], x_lvals: List[FNode],
                  symbs: FrozenSet[FNode],
                  locs: List[Location],
                  is_stutter: FNode, is_ranked: FNode,
                  is_gt0: FNode, is_eq0: FNode) -> Iterator[FNode]:
        assert isinstance(idx, int)
        assert isinstance(lvals, list)
        assert all(isinstance(val, FNode) for val in lvals)
        assert all(val in self.env.formula_manager.formulae.values()
                   for val in lvals)
        assert isinstance(x_lvals, list)
        assert all(isinstance(val, FNode) for val in x_lvals)
        assert all(val in self.env.formula_manager.formulae.values()
                   for val in x_lvals)
        assert isinstance(symbs, frozenset)
        assert all(isinstance(s, FNode) for s in symbs)
        assert all(s in self.env.formula_manager.get_all_symbols()
                   for s in symbs)
        assert isinstance(locs, list)
        assert all(isinstance(loc, Location) for loc in locs)
        assert isinstance(is_stutter, FNode)
        assert is_stutter in self.env.formula_manager.formulae.values()
        assert isinstance(is_ranked, FNode)
        assert is_ranked in self.env.formula_manager.formulae.values()
        assert isinstance(is_gt0, FNode)
        assert is_gt0 in self.env.formula_manager.formulae.values()
        assert isinstance(is_eq0, FNode)
        assert is_eq0 in self.env.formula_manager.formulae.values()

        mgr = self.env.formula_manager
        # cfg: loc -> \/ (x_loc & \/ trans_types)
        x_locs = []
        t_type = []
        if not self.stutterT.is_false():
            t_type.append(is_stutter)
        if not self.rankT.is_false():
            t_type.append(is_ranked)

        t_pair = self.progressT.get(idx)
        if t_pair is not None:
            assert isinstance(t_pair, tuple)
            assert len(t_pair) == 2
            if t_pair[TransType.EQ_0] is not None:
                t_type.append(is_eq0)
            if t_pair[TransType.GT_0] is not None:
                t_type.append(is_gt0)
        x_locs.append(mgr.And(x_lvals[idx], mgr.Or(t_type)))

        for dst, t_pair in self.progressT.items():
            t_type = []
            assert t_pair[TransType.EQ_0] is not None or \
                t_pair[TransType.GT_0] is not None
            if dst != idx:
                if t_pair[TransType.EQ_0] is not None:
                    t_type.append(is_eq0)
                if t_pair[TransType.GT_0] is not None:
                    t_type.append(is_gt0)
                if len(t_type) > 0:
                    x_locs.append(mgr.And(x_lvals[dst], mgr.Or(t_type)))

        yield mgr.Implies(lvals[idx], mgr.Or(x_locs))
        del x_locs, t_type

        # loc & loc' & is_stutter -> stutterT & rf' = rf
        if not self.stutterT.is_false():
            lhs = mgr.And(lvals[idx], x_lvals[idx], is_stutter)
            rhs = self.stutterT
            if self.rf is not None:
                rhs = mgr.And(rhs, self.rf.constant_pred())
            yield mgr.Implies(lhs, rhs)

        # loc & loc' & is_ranked -> rankT & rf' < rf
        if not self.rankT.is_false():
            assert self.rf is not None
            lhs = mgr.And(lvals[idx], x_lvals[idx], is_ranked)
            rhs = mgr.And(self.rankT, self.rf.progress_pred())
            yield mgr.Implies(lhs, rhs)

        # progress: gt_0 or eq_0
        _lhs = lvals[idx]
        if self.rf is not None:
            _lhs = mgr.And(lhs, mgr.Not(self.rf.is_ranked))
        for dst, t_pair in self.progressT.items():
            gt_0 = t_pair[TransType.GT_0]
            eq_0 = t_pair[TransType.EQ_0]
            assert gt_0 is not None or eq_0 is not None
            assert locs[dst].rf is not None or eq_0 is not None
            if gt_0 is not None:
                assert locs[dst].rf is not None
                x_ranked = to_next(mgr, locs[dst].rf.is_ranked, symbs)
                yield mgr.Implies(mgr.And(_lhs, x_lvals[dst], is_gt0),
                                  mgr.And(gt_0, x_ranked))
            if eq_0 is not None:
                rhs = eq_0
                if locs[dst].rf is not None:
                    x_ranked = to_next(mgr, locs[dst].rf.is_ranked, symbs)
                    rhs = mgr.And(rhs, mgr.Not(x_ranked))
                yield mgr.Implies(mgr.And(_lhs, is_eq0), rhs)

    def to_env(self, new_env: PysmtEnv) -> Location:
        """Return copy of self in the give environment"""
        assert isinstance(new_env, PysmtEnv)

        norm = new_env.formula_manager.normalize
        new_region = norm(self.region)
        new_assume = norm(self.assume)
        new_stutterT = norm(self.stutterT)
        new_rankT = norm(self.rankT)
        new_rf = self.rf.to_env(new_env) if self.rf is not None else None
        new_progressT = {idx: (norm(gt_0) if gt_0 is not None else None,
                               norm(eq_0) if eq_0 is not None else None)
                         for idx, (gt_0, eq_0) in self.progressT.items()}
        return Location(new_env, new_region, new_assume,
                        stutterT=new_stutterT, rankT=new_rankT, rf=new_rf,
                        progressT=new_progressT)


class Hint():
    """Transition system associated with:
    sequence of regions, assumptions and ranking functions.
    Represented as list of locations.
    """

    @staticmethod
    def disjoint_symbs(env: PysmtEnv, hints: List[Hint],
                       active: List[FNode]) -> Iterator[FNode]:
        """Return formulae that constrain active hints to have disjoint symbols"""
        assert isinstance(env, PysmtEnv)
        assert isinstance(hints, list)
        assert isinstance(active, list)
        assert all(isinstance(h, Hint) for h in hints)
        assert all(h.env == env for h in hints)
        assert all(isinstance(p, FNode) for p in active)
        assert all(p in env.formula_manager.formulae.values()
                   for p in active)
        assert len(hints) == len(active)
        mgr = env.formula_manager
        for idx, (h0, h0_active) in enumerate(zip(hints, active)):
            h_lst = []
            for h1, h1_active in zip(hints[idx+1:], active[idx+1: ]):
                if len(h0.owned_symbs & h1.owned_symbs) > 0:
                    h_lst.append(h1_active)
            if len(h_lst) > 0:
                yield mgr.Implies(h0_active,
                                  mgr.And(mgr.Not(p) for p in h_lst))


    def __init__(self, name: str, env: PysmtEnv,
                 owned_symbs: FrozenSet[FNode],
                 all_symbs: FrozenSet[FNode],
                 init: Optional[FNode] = None):
        assert isinstance(name, str)
        assert len(name) > 0
        assert isinstance(env, PysmtEnv)
        assert isinstance(owned_symbs, frozenset)
        assert all(isinstance(s, FNode) for s in owned_symbs)
        assert all(s in env.formula_manager.get_all_symbols()
                   for s in owned_symbs)
        assert all(symb_is_curr(s) for s in owned_symbs)
        assert isinstance(all_symbs, frozenset)
        assert all(isinstance(s, FNode) for s in all_symbs)
        assert all(s in env.formula_manager.get_all_symbols()
                   for s in all_symbs)
        assert all(symb_is_curr(s) for s in all_symbs)
        assert owned_symbs <= all_symbs
        assert init is None or isinstance(init, FNode)
        assert init is None or init in env.formula_manager.formulae.values()

        self.name = name
        self.env = env
        self.owned_symbs = owned_symbs
        self.all_symbs = all_symbs
        self.locs: List[Location] = []
        self.init = init if init is not None else env.formula_manager.TRUE()
        self.ts_loc_symbs = None
        self.ts_lvals = None
        self.trans_type_symbs = None
        self.t_is_stutter = None
        self.t_is_ranked = None
        self.t_is_eq0 = None
        self.t_is_gt0 = None

    def __str__(self) -> str:
        return self.name

    def __len__(self) -> int:
        return len(self.locs)

    def __getitem__(self, idx: int) -> Location:
        assert isinstance(idx, int)
        assert idx >= 0
        assert idx < len(self)
        return self.locs[idx]

    def __iter__(self) -> Iterator[Location]:
        assert isinstance(self.locs, list)
        assert all(isinstance(loc, Location) for loc in self.locs)
        return iter(self.locs)

    def add(self, loc: Location) -> None:
        assert self.ts_loc_symbs is None
        assert self.ts_lvals is None
        self.locs.append(loc)

    def set_locs(self, locs: List[Location]):
        assert isinstance(locs, list)
        assert all(isinstance(loc, Location) for loc in locs)
        assert all(loc.env == self.env for loc in locs)
        assert self.ts_loc_symbs is None
        assert self.ts_lvals is None
        self.locs = locs

    def get_trans_system(self, active: FNode) -> Tuple[FrozenSet[FNode],
                                                       List[FNode], List[FNode],
                                                       FNode]:
        """Return encoding of Hint as an activable transition system:
        Transition system with flag to enable/disable.
        Return <set of newly introduced symbols, Init, Trans, active>
        """
        assert isinstance(active, FNode)
        assert active in self.env.formula_manager.formulae.values()

        mgr = self.env.formula_manager
        if self.ts_loc_symbs is None:
            assert self.ts_lvals is None
            self.ts_loc_symbs, self.ts_lvals = new_enum(self.env,
                                                        f"{self.name}_",
                                                        len(self) + 1)
            assert len(self.ts_lvals) == len(self) + 1
            self.trans_type_symbs, trans_type_vals = new_enum(
                self.env, f"{self.name}_type_", len(TransType))
            assert len(trans_type_vals) == len(TransType)
            (self.t_is_stutter, self.t_is_ranked,
             self.t_is_gt0, self.t_is_eq0) = trans_type_vals
        assert self.ts_loc_symbs is not None
        assert self.ts_lvals is not None
        assert self.trans_type_symbs is not None
        assert self.t_is_stutter is not None
        assert self.t_is_ranked is not None
        assert self.t_is_gt0 is not None
        assert self.t_is_eq0 is not None

        new_symbs = frozenset(chain(self.ts_loc_symbs, self.trans_type_symbs))
        lvals = self.ts_lvals
        x_lvals = [to_next(mgr, lval, new_symbs) for lval in lvals]
        symbs = frozenset.union(self.all_symbs, new_symbs)
        inactive = lvals[-1]
        x_inactive = x_lvals[-1]
        x_t_is_stutter = to_next(mgr, self.t_is_stutter, symbs)
        # invar: loc = i -> region(i) & assume(i)
        init = [mgr.Implies(l_val, mgr.And(loc.region, loc.assume))
                for l_val, loc in zip(lvals, self.locs)]
        # invar: inactive | (\/ loc = i)
        init.append(mgr.Or(lvals))
        trans = [to_next(mgr, pred, symbs) for pred in init]

        n_active = mgr.Not(active)
        # init: ! active -> inactive
        init.append(mgr.Implies(n_active, inactive))
        # init: trans_type = stutter
        init.append(self.t_is_stutter)
        # trans: ! active -> inactive' & t_is_stutter'
        trans.append(mgr.Implies(n_active, mgr.And(x_inactive, x_t_is_stutter)))
        if not self.init.is_true():
            # loc = -1 & loc' != -1 -> init
            trans.append(mgr.Implies(mgr.And(inactive, mgr.Not(x_inactive)),
                                     self.init))
        trans.extend(chain.from_iterable(
            loc.get_trans(idx, lvals, x_lvals, symbs, self.locs,
                          self.t_is_stutter, self.t_is_ranked,
                          self.t_is_gt0, self.t_is_eq0)
            for idx, loc in enumerate(self.locs)))

        return new_symbs, init, trans, mgr.Not(inactive)

    def to_env(self, new_env: PysmtEnv) -> Hint:
        """Return copy of self in the give environment"""
        assert isinstance(new_env, PysmtEnv)

        norm = new_env.formula_manager.normalize
        new_owned = frozenset(norm(s) for s in self.owned_symbs)
        new_all_symbs = frozenset(norm(s) for s in self.all_symbs)
        new_init = norm(self.init)
        new_locs = [loc.to_env(new_env) for loc in self.locs]
        res = Hint(self.name, new_env, new_owned, new_all_symbs, new_init)
        res.set_locs(new_locs)
        return res

    def is_correct(self) -> Tuple[Optional[bool], List[str]]:
        """Returns true iff current hint satisfies all required hypotheses.
        In case some property is violated, the string contains a description
        of the error."""
        # Check indexes.
        for src_idx, src_l in enumerate(self):
            for dst_idx in src_l.dsts:
                if dst_idx >= len(self):
                    return False, f"unknown destination {dst_idx} of " \
                        f"{src_idx}: out of bound"
        generalise = Generaliser(self.env, Canonizer(env=self.env),
                                  ExprAtTime(env=self.env))
        msgs = []
        correct = True
        for check in [# self._is_stutter_correct,
                      # self._is_rank_correct,
                      # self._is_progress0_correct,
                      self._is_progress1_correct]:
            res, msg = check(generalise=generalise)
            if not res:
                correct = correct if correct is False else res
                msgs.append(msg)
        return correct, msgs

    def _is_stutter_correct(self, generalise=None) -> Tuple[Optional[bool],
                                                            Optional[str]]:
        """Check stutter transition of every location."""
        mgr = self.env.formula_manager
        other_symbs = self.all_symbs - self.owned_symbs
        x_own_symbs = frozenset(symb_to_next(mgr, s)
                                for s in self.owned_symbs)
        x_other_symbs = frozenset(symb_to_next(mgr, s)
                                  for s in other_symbs)
        for src_idx, src_l in enumerate(self):
            region = src_l.region
            x_region = to_next(mgr, region, self.all_symbs)
            assume = src_l.assume
            x_assume = to_next(mgr, assume, self.all_symbs)
            stutterT = src_l.stutterT
            if src_l.rf is not None:
                rf_expr = src_l.rf.expr
                x_rf_expr = to_next(mgr, rf_expr, self.all_symbs)
                stutterT = mgr.And(stutterT, mgr.Equals(x_rf_expr, rf_expr))
            exists = False
            with MultiSolver(self.env, get_timeout()) as solver:
                solver.add_assertions([region, assume, stutterT,
                                       x_region, x_assume])
                try:
                    exists = solver.solve()
                except SolverReturnedUnknownResultError:
                    return None, f"{self.name}: stutter on {src_idx} might be empty"
            if exists:
                constr = mgr.Implies(mgr.And(region, assume, x_assume),
                                     mgr.And(stutterT, x_region))
                model, _ = efesolve(self.env, self.all_symbs, x_own_symbs,
                                    x_other_symbs,
                                    mgr.Not(constr),
                                    generalise=generalise)
                if model is None:
                    return None, f"{self.name}: stutter trans hyp on {src_idx} unknown"
                if model is not False:
                    return False, f"{self.name}: stutter trans hyp on {src_idx} violated"
        return True, None

    def _is_rank_correct(self, generalise=None) -> Tuple[Optional[bool],
                                                         Optional[str]]:
        """Check ranked transition for every location."""
        mgr = self.env.formula_manager
        other_symbs = self.all_symbs - self.owned_symbs
        x_own_symbs = frozenset(symb_to_next(mgr, s)
                                for s in self.owned_symbs)
        x_other_symbs = frozenset(symb_to_next(mgr, s)
                                  for s in other_symbs)
        for src_idx, src_l in enumerate(self):
            if src_l.rf is None:
                continue
            x_region = to_next(mgr, src_l.region, self.all_symbs)
            region = src_l.ranked_region
            assume = src_l.assume
            x_assume = to_next(mgr, assume, self.all_symbs)
            rf_expr = src_l.rf.expr
            rf_delta = src_l.rf.delta
            x_rf_expr = to_next(mgr, rf_expr, self.all_symbs)
            rankT = mgr.And(src_l.rankT,
                            mgr.LE(x_rf_expr, mgr.Minus(rf_expr, rf_delta)))

            exists = False
            with MultiSolver(self.env, get_timeout()) as solver:
                solver.add_assertions([region, assume, rankT,
                                       x_region, x_assume])
                try:
                    exists = solver.solve()
                except SolverReturnedUnknownResultError:
                    return None, f"{self.name}: ranked trans on {src_idx} might be empty"
            if exists:
                constr = mgr.Implies(mgr.And(region, assume, x_assume),
                                     mgr.And(rankT, x_region))
                model, _ = efesolve(self.env, self.all_symbs, x_own_symbs,
                                    x_other_symbs,
                                    mgr.Not(constr),
                                    generalise=generalise)
                if model is None:
                    return None, f"{self.name}: ranked trans hyp on {src_idx} unknown"
                if model is not False:
                    return False, f"{self.name}: ranked trans hyp on {src_idx} violated"
        return True, None

    def _is_progress0_correct(self, generalise=None) -> Tuple[Optional[bool],
                                                              Optional[str]]:
        """Check progress transition reaching rf > 0."""
        mgr = self.env.formula_manager
        other_symbs = self.all_symbs - self.owned_symbs
        x_own_symbs = frozenset(symb_to_next(mgr, s)
                                for s in self.owned_symbs)
        x_other_symbs = frozenset(symb_to_next(mgr, s)
                                  for s in other_symbs)
        for src_idx, src_l in enumerate(self):
            src = [src_l.region, src_l.assume]
            if src_l.rf is not None:
                src.append(mgr.Not(src_l.rf.is_ranked))
            src = mgr.And(src)
            for dst_idx in src_l.dsts:
                progressT = src_l.progress_gt_0(dst_idx)
                dst_l = self[dst_idx]
                if dst_l.rf is None:
                    continue
                x_region = to_next(mgr, dst_l.region, self.all_symbs)
                x_assume = to_next(mgr, dst_l.assume, self.all_symbs)
                x_ranked = to_next(mgr, dst_l.rf.is_ranked, self.all_symbs)
                exists = False
                with MultiSolver(self.env, get_timeout()) as solver:
                    solver.add_assertions([src, progressT, x_region,
                                           x_assume, x_ranked])
                    try:
                        exists = solver.solve()
                    except SolverReturnedUnknownResultError:
                        return None, "{self.name}: progress0 trans " \
                            f"{src_idx} - {dst_idx} might be empty"
                if exists:
                    constr = mgr.Implies(mgr.And(src, x_assume),
                                         mgr.And(progressT, x_region, x_ranked))
                    model, _ = efesolve(self.env, self.all_symbs, x_own_symbs,
                                        x_other_symbs,
                                        mgr.Not(constr),
                                        generalise=generalise)
                    if model is None:
                        return None, f"{self.name}: progress0 hyp {src_idx} -> " \
                            f"{dst_idx} unknown"
                    if model is not False:
                        return False, f"{self.name}: progress0 hyp {src_idx} -> " \
                            f"{dst_idx} violated"
        return True, None

    def _is_progress1_correct(self, generalise=None) -> Tuple[Optional[bool],
                                                              Optional[str]]:
        """Check progress transition reaching rf = 0."""
        mgr = self.env.formula_manager
        other_symbs = self.all_symbs - self.owned_symbs
        x_own_symbs = frozenset(symb_to_next(mgr, s)
                                for s in self.owned_symbs)
        x_other_symbs = frozenset(symb_to_next(mgr, s)
                                  for s in other_symbs)
        for src_idx, src_l in enumerate(self):
            src = [src_l.region, src_l.assume]
            if src_l.rf is not None:
                src.append(mgr.Not(src_l.rf.is_ranked))
            src = mgr.And(src)
            for dst_idx in src_l.dsts:
                progressT = src_l.progress_eq_0(dst_idx)
                dst_l = self[dst_idx]
                x_region = to_next(mgr, dst_l.region, self.all_symbs)
                x_assume = to_next(mgr, dst_l.assume, self.all_symbs)
                if dst_l.rf is not None:
                    x_not_ranked = to_next(mgr, mgr.Not(dst_l.rf.is_ranked),
                                           self.all_symbs)
                    x_region = mgr.And(x_region, x_not_ranked)
                exists = False
                with MultiSolver(self.env, get_timeout()) as solver:
                    solver.add_assertions([src, progressT, x_region,
                                           x_assume])
                    try:
                        exists = solver.solve()
                    except SolverReturnedUnknownResultError:
                        return None, "{self.name}: progress1 trans " \
                            f"{src_idx} - {dst_idx} might be empty"
                if exists:
                    constr = mgr.Implies(mgr.And(src, x_assume),
                                         mgr.And(progressT, x_region))
                    model, _ = efesolve(self.env, self.all_symbs, x_own_symbs,
                                        x_other_symbs, mgr.Not(constr),
                                        generalise=generalise)
                    if model is None:
                        return None, f"{self.name}: progress1 hyp {src_idx} -> " \
                            f"{dst_idx} unknown"
                    if model is not False:
                        return False, f"{self.name}: progress1 hyp {src_idx} -> " \
                            f"{dst_idx} violated"
        return True, None
