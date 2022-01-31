from __future__ import annotations
from typing import (FrozenSet, Set, List, Dict, Tuple, Iterator, Iterable,
                    Union, Optional)
from re import compile as mk_re
from io import StringIO
from itertools import chain

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
from pysmt.solvers.solver import Model
from pysmt.typing import REAL as PyReal

from rankfun import RankFun, IRankFun, RRankFun
from expr_at_time import ExprAtTime
from canonize import Canonizer
from implicant import Implicant
from funnel import Funnel, RFFunnel
from efsolver import efmultisolve
from motzkin import motzkin_solve
from expr_utils import (assigns2fnodes, linear_comb, new_param,
                        not_rel, get_times, symb_is_next)
from utils import log


class FLoopGen:
    """Generator of Funnel-loops"""

    _LOG_LVL = 1
    _MIN_LOOP_REPS = 1
    # _RE_LOOP = (r"(?<!\d)(?P<base>(?:(?:(?:\d+-\d+)|(?:f\d+));)*)"
    #             r"(?:(?P<last_f>f\d+)|(?:(?P<last_r>\d+)-(?P<lback>\d+)));"
    #             r"(?:(?P=base)(?:(?P=last_f)|(?:(?P=last_r)-(?P=lback)));){{{},}}"
    #             r"(?:(?P=base)(?:(?P=last_f)|"
    #             r"(?:(?P=last_r)-(?:(?P=lback)|(?P<exit>\d+)))))")
    _RE_LOOP = (r"(?<!\d)"  # cannot start in the middle of a number.
                r"(?P<base>(?:(?:(?:\d+-\d+)|(?:f\d+));)+)(?P=base){{{},}}")

    @staticmethod
    def get_min_loop_reps() -> int:
        return FLoopGen._MIN_LOOP_REPS

    @staticmethod
    def set_min_loop_reps(val: int) -> None:
        assert isinstance(val, int)
        FLoopGen._MIN_LOOP_REPS = val

    @staticmethod
    def get_log_lvl() -> int:
        return FLoopGen._LOG_LVL

    @staticmethod
    def set_log_lvl(val: int) -> None:
        assert isinstance(val, int)
        FLoopGen._LOG_LVL = val

    def __init__(self, env: PysmtEnv, totime: ExprAtTime,
                 cn: Canonizer):
        assert isinstance(env, PysmtEnv)
        assert isinstance(totime, ExprAtTime)
        assert isinstance(cn, Canonizer)
        self.env = env
        self.totime = totime
        self.cn = cn
        self._re_loop = mk_re(FLoopGen._RE_LOOP.format(
            FLoopGen.get_min_loop_reps()))

    def make_lasso(self, symbs: FrozenSet[FNode], trace: Model,
                   first: int, last: int) -> FLoop:
        assert isinstance(symbs, frozenset)
        assert all(isinstance(s, FNode) for s in symbs)
        assert all(s.is_symbol() for s in symbs)
        assert all(s in self.env.formula_manager.get_all_symbols()
                   for s in symbs)
        assert hasattr(trace, "get_value")
        assert isinstance(first, int)
        assert isinstance(last, int)
        assert 0 <= first < last
        assigns = [{s: trace.get_value(self.totime(s, idx)) for s in symbs}
                   for idx in range(first, last)]
        assert assigns[0] == {s: trace.get_value(self.totime(s, last))
                              for s in symbs}
        assert len(assigns) == last - first
        empty: List[Set[FNode]] = [set()] * len(assigns)
        empty_eqs: List[Dict[FNode, FNode]] = [{}] * len(assigns)
        return FLoop([Funnel(self.env, 0, frozenset(), assigns, assigns,
                             empty, empty_eqs, empty, empty, empty,
                             self.totime, self.cn)])

    def gen(self, loop_states: List[Dict[FNode, FNode]],
            symbs: FrozenSet[FNode],
            assigns: List[Dict[FNode, FNode]],
            regions: List[Set[FNode]],
            trans: List[Set[FNode]],
            h_regions: List[Set[FNode]],
            h_trans: List[Set[FNode]],
            h_rfs: Dict[Tuple[int, int], RankFun],
            rfs: Set[RankFun]) -> Iterator[FLoop]:
        assert isinstance(loop_states, list)
        assert all(isinstance(step, dict) for step in loop_states)
        assert all(isinstance(s, FNode) for step in loop_states
                   for s in step)
        assert all(isinstance(v, FNode) for step in loop_states
                   for v in step.values())
        assert all(s in self.env.formula_manager.get_all_symbols()
                   for step in loop_states for s in step)
        assert all(v in self.env.formula_manager.formulae.values()
                   for step in loop_states for v in step.values())
        assert all(v.is_constant() for step in loop_states
                   for v in step.values())
        assert isinstance(symbs, frozenset)
        assert len(symbs) > 0
        assert all(isinstance(s, FNode) for s in symbs)
        assert all(s in self.env.formula_manager.get_all_symbols()
                   for s in symbs)
        assert isinstance(assigns, list)
        assert len(assigns) == len(loop_states)
        assert all(isinstance(assign, dict) for assign in assigns)
        assert all(isinstance(k, FNode) for assign in assigns for k in assign)
        assert all(k in self.env.formula_manager.get_all_symbols()
                   for assign in assigns for k in assign)
        assert all(isinstance(v, FNode) for assign in assigns
                   for v in assign.values())
        assert all(v in self.env.formula_manager.formulae.values()
                   for assign in assigns for v in assign)
        assert isinstance(regions, list)
        assert len(regions) == len(assigns)
        assert all(isinstance(reg, set) for reg in regions)
        assert all(isinstance(p, FNode) for r in regions for p in r)
        assert all(p in self.env.formula_manager.formulae.values()
                   for r in regions for p in r)
        assert isinstance(trans, list)
        assert len(trans) == len(assigns)
        assert all(isinstance(tr, set) for tr in trans)
        assert all(isinstance(p, FNode) for tr in trans for p in tr)
        assert all(p in self.env.formula_manager.formulae.values()
                   for tr in trans for p in tr)
        assert isinstance(h_regions, list)
        assert len(h_regions) == len(assigns)
        assert all(isinstance(reg, set) for reg in h_regions)
        assert all(isinstance(p, FNode) for r in h_regions for p in r)
        assert all(p in self.env.formula_manager.formulae.values()
                   for r in h_regions for p in r)
        assert isinstance(h_trans, list)
        assert len(h_trans) == len(assigns)
        assert all(isinstance(tr, set) for tr in h_trans)
        assert all(isinstance(p, FNode) for tr in h_trans for p in tr)
        assert all(p in self.env.formula_manager.formulae.values()
                   for tr in h_trans for p in tr)
        assert isinstance(h_rfs, dict)
        assert all(isinstance(k, tuple) for k in h_rfs)
        assert all(len(k) == 2 for k in h_rfs)
        assert all(isinstance(k[0], int) and isinstance(k[1], int)
                   for k in h_rfs)
        assert all(0 <= k[0] <= k[1] < len(regions) for k in h_rfs)
        assert all(isinstance(rf, RankFun) for rf in h_rfs.values())
        assert all(rf.env == self.env for rf in h_rfs.values())
        assert isinstance(rfs, set)
        assert all(isinstance(rf, RankFun) for rf in rfs)
        assert all(rf.env == self.env for rf in rfs)

        set2id: Dict[FrozenSet[FNode], int] = {}
        regids = []
        for idx, (eqs, reg, h_reg) in enumerate(zip(assigns, regions,
                                                    h_regions)):
            k = frozenset(chain(assigns2fnodes(self.env, eqs), reg | h_reg))
            reg_id = set2id.get(k)
            if reg_id is None:
                reg_id = idx
                set2id[k] = reg_id
            regids.append(reg_id)
        set2id.clear()
        trids = []
        for idx, (tr, h_tr) in enumerate(zip(trans, h_trans)):
            k = frozenset(tr | h_tr)
            tr_id = set2id.get(k)
            if tr_id is None:
                tr_id = idx
                set2id[k] = tr_id
            trids.append(tr_id)
        assert len(regids) == len(trids)
        l_str = f"{';'.join('-'.join(str(i) for i in el) for el in zip(regids, trids))};"
        log(f"\tFind inner loops on str: {l_str}", FLoopGen.get_log_lvl())
        last_end = 0
        fnls: List[Funnel] = []
        first_reg_ids, first_tr_ids = [], []
        for m in self._re_loop.finditer(l_str):
            m_start, m_end = m.span()
            assert l_str[m_start] != ';'
            assert l_str[m_end - 1] == ';'
            assert last_end <= m_start < len(l_str)
            # Instantiate Funnel from "skipped" regions.
            if m_start > last_end:
                assert last_end == 0 or l_str[:last_end].endswith(';')
                assert l_str[last_end: m_start].endswith(';')
                assert not l_str[last_end: m_start].startswith(';')
                reg_ids, tr_ids = self._parse_base(l_str[last_end: m_start-1])
                # Do not begin FLoop with Funnel, prefer RFFunnel.
                # Avoid having a Funnel both at the beginning and at the end.
                if last_end == 0:
                    first_reg_ids, first_tr_ids = reg_ids, tr_ids
                else:
                    fnls.append(Funnel(self.env, reg_ids[0], symbs,
                                       [loop_states[idx] for idx in reg_ids],
                                       [assigns[idx] for idx in reg_ids],
                                       [regions[idx] for idx in reg_ids],
                                       [{} for idx in tr_ids],
                                       [trans[idx] for idx in tr_ids],
                                       [h_regions[idx] for idx in reg_ids],
                                       [h_trans[idx] for idx in tr_ids],
                                       self.totime, self.cn))
            last_end = m_end
            # Instantiate RFFunnel for matched sequence.
            reg_ids, tr_ids = self._match2fnl(m)
            assert len(reg_ids) > 0
            assert len(reg_ids) == len(tr_ids)
            fnls.append(RFFunnel(self.env, reg_ids[0], symbs,
                                 [loop_states[idx] for idx in reg_ids],
                                 [assigns[idx] for idx in reg_ids],
                                 [regions[idx] for idx in reg_ids],
                                 [{} for idx in tr_ids],
                                 [trans[idx] for idx in tr_ids],
                                 [h_regions[idx] for idx in reg_ids],
                                 [h_trans[idx] for idx in tr_ids],
                                 self.totime, self.cn))
        if len(fnls) > 0:
            if last_end < len(l_str) - 1:
                assert last_end == 0 or l_str[:last_end].endswith(';')
                assert not l_str[last_end:].startswith(';')
                assert l_str[last_end:].endswith(';')
                assert len(l_str[last_end: -1]) >= 3
                reg_ids, tr_ids = self._parse_base(l_str[last_end:-1])
                reg_ids.extend(first_reg_ids)
                tr_ids.extend(first_tr_ids)
                fnls.append(Funnel(self.env, reg_ids[0], symbs,
                                   [loop_states[idx] for idx in reg_ids],
                                   [assigns[idx] for idx in reg_ids],
                                   [regions[idx] for idx in reg_ids],
                                   [{} for idx in tr_ids],
                                   [trans[idx] for idx in tr_ids],
                                   [h_regions[idx] for idx in reg_ids],
                                   [h_trans[idx] for idx in tr_ids],
                                   self.totime, self.cn))
            elif len(first_reg_ids) > 0:
                assert len(first_reg_ids) == len(first_tr_ids)
                fnls.append(Funnel(self.env, reg_ids[0], symbs,
                                   [loop_states[idx] for idx in first_reg_ids],
                                   [assigns[idx] for idx in first_reg_ids],
                                   [regions[idx] for idx in first_reg_ids],
                                   [{} for idx in first_tr_ids],
                                   [trans[idx] for idx in first_tr_ids],
                                   [h_regions[idx] for idx in first_reg_ids],
                                   [h_trans[idx] for idx in first_tr_ids],
                                   self.totime, self.cn))
            assert len(fnls) > 0
            yield FLoop(fnls)

        # single Funnel.
        fnl = Funnel(self.env, 0, symbs, loop_states,
                     assigns, regions, [{} for _ in trans],
                     trans, h_regions, h_trans, self.totime, self.cn)
        yield FLoop([fnl])

    def _match2fnl(self, match) -> Tuple[List[int], List[int]]:
        assert len(match.groups()) > 0
        assert len(match[1]) >= 4
        assert match[1] == match.groupdict()["base"]
        assert match[1].endswith(';')
        return self._parse_base(match[1][:-1])

    def _parse_base(self, base: str) -> Tuple[List[int], List[int]]:
        assert isinstance(base, str)
        assert len(base) >= 3
        assert not base.startswith(';'), base
        assert not base.endswith(';'), base
        regs: List[int] = []
        trans: List[int] = []
        for item in base.split(';'):
            el = item.split('-')
            assert len(el) == 2
            regs.append(int(el[0]))
            trans.append(int(el[1]))
        assert len(regs) > 0
        assert len(regs) == len(trans)
        return regs, trans


class FLoop():

    _LOG_LVL = 1
    _PROPAGATE_MAX_IT = 2
    _MIN_INEQS = 0
    _MAX_INEQS = 2
    _RM_DEADLOCKS = True
    _RM_REDUNDANT = True
    _PREINST_INNER_RF = True

    @staticmethod
    def get_log_lvl() -> int:
        return FLoop._LOG_LVL

    @staticmethod
    def set_log_lvl(val: int) -> None:
        assert isinstance(val, int)
        FLoop._LOG_LVL = val

    @staticmethod
    def set_propagate_max_it(val: int) -> None:
        assert isinstance(val, int), val
        assert val >= 1
        FLoop._PROPAGATE_MAX_IT = val

    @staticmethod
    def get_propagate_max_it() -> int:
        return FLoop._PROPAGATE_MAX_IT

    @staticmethod
    def set_min_ineqs(val: int) -> None:
        assert isinstance(val, int), val
        assert val >= 0
        FLoop._MIN_INEQS = val

    @staticmethod
    def get_min_ineqs() -> int:
        return FLoop._MIN_INEQS

    @staticmethod
    def set_max_ineqs(val: int) -> None:
        assert isinstance(val, int), val
        assert val >= 0
        FLoop._MAX_INEQS = val

    @staticmethod
    def get_max_ineqs() -> int:
        return FLoop._MAX_INEQS

    @staticmethod
    def set_rm_deadlocks(val: bool) -> None:
        assert isinstance(val, bool), val
        FLoop._RM_DEADLOCKS = val

    @staticmethod
    def get_rm_deadlocks() -> bool:
        return FLoop._RM_DEADLOCKS

    @staticmethod
    def set_rm_redundant(val: bool) -> None:
        assert isinstance(val, bool), val
        FLoop._RM_REDUNDANT = val

    @staticmethod
    def get_rm_redundant() -> bool:
        return FLoop._RM_REDUNDANT

    @staticmethod
    def set_preinst_inner_rf(val: bool) -> None:
        assert isinstance(val, bool), val
        FLoop._PREINST_INNER_RF = val

    @staticmethod
    def get_preinst_inner_rf() -> bool:
        return FLoop._PREINST_INNER_RF

    def __init__(self, fnls: List[Funnel]):
        assert isinstance(fnls, list)
        assert len(fnls) > 0
        assert all(isinstance(fnl, Funnel) for fnl in fnls)
        assert all(fnl.env == fnls[0].env for fnl in fnls[1:])
        assert all(fnl.symbs == fnls[0].symbs for fnl in fnls[1:])
        self.fnls = fnls

    @property
    def first_state(self) -> Dict[FNode, FNode]:
        assert len(self.fnls) > 0
        assert len(self.fnls[0].states) > 0
        return self.fnls[0].states[0]

    def __str__(self) -> str:
        with StringIO() as buf:
            self.serialize(buf)
            return buf.getvalue()

    def serialize(self, buf) -> None:
        serialize = self.fnls[0].env.serializer.serialize
        idx = 0
        buf.write("\tReachable state: ")
        buf.write("; ".join(f"{serialize(s)}: {serialize(self.first_state[s])}"
                            for s in sorted(self.first_state,
                                            key=lambda s: s.symbol_name())))
        buf.write(";\n")
        for fnl in self.fnls:
            idx = fnl.write_hr(idx, buf)

    def rfs(self) -> Iterator[RankFun]:
        for fnl in self.fnls:
            if isinstance(fnl, RFFunnel):
                yield fnl.rf

    def candidate_steps(self, last_idx: int) -> Iterator[List[FNode]]:
        assert isinstance(last_idx, int)
        assert last_idx > 0
        assert len(self.fnls) > 0
        env = self.fnls[0].env
        ends = [fnl.first_idx for fnl in self.fnls[1:]]
        ends.append(self.fnls[0].first_idx)
        assert all(end < last_idx for end in ends)
        assert all((fnl.first_idx + len(fnl.regs) % last_idx) <= end
                   for fnl, end in zip(self.fnls, ends))
        assert all(isinstance(fnl, RFFunnel) or
                   (fnl.first_idx + len(fnl.regs) % last_idx) == end
                   for fnl, end in zip(self.fnls, ends))
        for fnl, end in zip(self.fnls, ends):
            start = fnl.first_idx
            assert len(fnl.assigns) > 0
            assert len(fnl.regs) == len(fnl.assigns)
            assert len(fnl.h_regs) == len(fnl.assigns)
            assert len(fnl.t_eqs) == len(fnl.assigns)
            assert len(fnl.trans) == len(fnl.assigns)
            assert len(fnl.h_trans) == len(fnl.assigns)
            assert isinstance(fnl, RFFunnel) or \
                end == (start + len(fnl.regs)) % last_idx
            res = [list(chain(assigns2fnodes(env, assign), reg, h_reg,
                              assigns2fnodes(env, eq), tr, h_tr))
                   for assign, reg, h_reg, eq, tr, h_tr in
                   zip(fnl.assigns, fnl.regs, fnl.h_regs, fnl.t_eqs,
                       fnl.trans, fnl.h_trans)]
            assert len(res) == len(fnl.regs)
            assert start < last_idx
            if end <= start:
                end += last_idx
            assert start < end
            while start < end:
                yield from res
                start = start + len(fnl.regs)

    def repl_constants(self, state: Dict[FNode, FNode]) -> FrozenSet[FNode]:
        assert all(self.fnls[0].symbs == fnl.symbs for fnl in self.fnls[1:])
        # find candidate constants for each funnel.
        lasso_symbs = frozenset(s for s in self.fnls[0].symbs
                                if state[s] == self.first_state[s])
        last_state = self.fnls[0].states[0]
        last_reg = self.fnls[0].regs[0]
        last_h_reg = self.fnls[0].h_regs[0]
        for fnl in reversed(self.fnls):
            lasso_symbs = fnl.filter_constant_symbs(lasso_symbs, last_state,
                                                    last_reg, last_h_reg)
            last_state = fnl.states[0]
            last_reg, last_h_reg = fnl.regs[0], fnl.h_regs[0]
        if len(lasso_symbs) > 0:
            serialize = self.fnls[0].env.serializer.serialize
            log("\tConstant symbs: "
                f"{', '.join(serialize(s) for s in lasso_symbs)}.",
                FLoop.get_log_lvl())
            # replace constants with concrete value.
            for fnl in reversed(self.fnls):
                fnl.mk_symbs_constant(lasso_symbs, state)
                state = fnl.states[0]
        return lasso_symbs

    def _check_first_state(self, impl: Implicant) \
            -> Optional[Tuple[int, FNode]]:
        assert isinstance(impl, Implicant)
        assert len(self.fnls) > 0
        assert self.first_state is not None
        assert all(not p.is_false() for p in self.fnls[0].first())
        env = impl.env
        mgr = env.formula_manager
        simpl = env.simplifier.simplify
        subst = env.substituter.substitute
        res = []
        itp_fms = []
        # Here we assume that the interpolator supports the combination of the theories.
        for p in self.fnls[0].first():
            if Implicant.is_itp_supported(impl.env, p):
                itp_fms.append(p)
            elif simpl(subst(p, self.first_state)).is_false():
                res.append(p)
        if any(simpl(subst(p, self.first_state)).is_false()
               for p in itp_fms):
            # Compute itp: reg -> itp & itp -> !state
            # itp = frozenset(p for p in reg if simpl(subst(p, state)).is_false())
            with impl.env.factory.Interpolator() as interp:
                itp = interp.binary_interpolant(
                    mgr.And(itp_fms),
                    mgr.And(assigns2fnodes(env, self.first_state)))
                assert itp is not None
                res.append(itp)
        if len(res) == 0:
            assert all(not simpl(subst(p, self.first_state)).is_false()
                   for p in self.fnls[0].first())
            return None
        res = mgr.And(res)
        if __debug__:
            from solver import Solver
            # preds -> res
            with Solver(env=env) as _solver:
                _solver.add_assertion(mgr.And(self.fnls[0].first()))
                _solver.add_assertion(mgr.Not(res))
                assert _solver.solve() is False
            # res -> !state
            with Solver(env=env) as _solver:
                _solver.add_assertion(res)
                _solver.add_assertion(mgr.And(
                    assigns2fnodes(env, self.first_state)))
                assert _solver.solve() is False
        assert self.fnls[0].first_idx >= 0
        return self.fnls[0].first_idx, res

    def back_prop(self, impl: Implicant) -> \
            Optional[Tuple[int, Optional[FNode]]]:
        assert isinstance(impl, Implicant)
        assert impl.env == self.fnls[0].env
        for it in range(1, FLoop.get_propagate_max_it() + 1):
            log(f"\tFLoop preds backward propagation iteration {it}.",
                FLoop.get_log_lvl())
            prev_idx = 0
            for idx in range(len(self.fnls) - 1, -1, -1):
                prev_fnl = self.fnls[prev_idx]
                fnl = self.fnls[idx]
                not_empty, keep, h_keep = \
                    fnl.back_prop(prev_fnl.regs[0], prev_fnl.h_regs[0], impl)
                if not_empty is False:
                    return -1, None
                if prev_idx != 0:
                    prev_fnl.impl_reg = prev_fnl.regs[0] - keep
                    prev_fnl.regs[0] = keep
                    prev_fnl.h_impl_reg = prev_fnl.h_regs[0] - h_keep
                    prev_fnl.h_regs[0] = h_keep

                prev_idx = idx
        return self._check_first_state(impl)

    def rm_redundant_preds(self, impl: Implicant) -> \
            Optional[Tuple[int, Optional[FNode]]]:
        assert isinstance(impl, Implicant)
        assert impl.env == self.fnls[0].env
        if FLoop.get_rm_redundant():
            log("\tFLoop remove redundant predicates.",
                FLoop.get_log_lvl())
            if any(fnl.rm_redundant(impl) is False for fnl in self.fnls):
                # TODO compute itp return idx + self.first_idx, itp
                return -1, None
        return self._check_first_state(impl)

    def rm_deadlocks(self, impl) -> Optional[Tuple[int, Optional[FNode]]]:
        assert isinstance(impl, Implicant)
        assert impl.env == self.fnls[0].env
        if FLoop.get_rm_deadlocks():
            n_refs = 0
            log("\tFLoop remove deadlocks.", FLoop.get_log_lvl())
            prev_fnl = self.fnls[0]
            for idx in reversed(range(len(self.fnls))):
                fnl = self.fnls[idx]
                n = fnl.rm_deadlocks(chain(prev_fnl.regs[0],
                                           prev_fnl.h_regs[0]),
                                     impl)
                if n == -1:
                    # TODO compute itp return idx + self.first_idx, itp
                    return -1, None
                if n > 0:
                    not_empty, keep, h_keep = fnl.back_prop([], [], impl)
                    assert len(keep) == 0
                    assert len(h_keep) == 0
                    if not_empty is False:
                        return -1, None
                    n_refs += n
                prev_fnl = fnl
            log(f"\tFLoop learned {n_refs} preds to remove deadlocks.",
                FLoop.get_log_lvl())
        return self._check_first_state(impl)

    def uapprox_trans(self, x_h_symbs: FrozenSet[FNode]) -> None:
        assert isinstance(x_h_symbs, frozenset)
        assert all(isinstance(s, FNode) for s in x_h_symbs)
        assert all(s in self.fnls[0].env.formula_manager.get_all_symbols()
                   for s in x_h_symbs)
        assert all(symb_is_next(s) for s in x_h_symbs)
        for fnl in self.fnls:
            fnl.uapprox_trans(fnl.x_symbs - x_h_symbs)

    def uapprox_regs(self) -> Iterator[Tuple[int, FLoop]]:
        for fnl in self.fnls:
            fnl.uapprox_regs(FLoop.get_min_ineqs())
        yield FLoop.get_min_ineqs(), self
        for num in range(FLoop.get_min_ineqs() + 1, FLoop.get_max_ineqs() + 1):
            for fnl in self.fnls:
                fnl.uapprox_regs(1)
            yield num, self

    def inst_inner_rfs(self, impl: Implicant) -> Set[RankFun]:
        """Try instantiate rfs for inner loops"""
        assert isinstance(impl, Implicant)
        assert impl.env == self.fnls[0].env
        res: Set[RankFun] = set()
        if not FLoop.get_preinst_inner_rf():
            return res
        fnls = [(idx, fnl) for idx, fnl in enumerate(self.fnls)
                if isinstance(fnl, RFFunnel)]
        if len(fnls) == 0:
            return res
        log("\tFLoop try instantiate ranking functions for inner loops.",
            FLoop.get_log_lvl())
        for idx, fnl in fnls:
            assert isinstance(fnl, RFFunnel)
            x_fnl = self.fnls[(idx + 1) % len(self.fnls)]
            res.add(fnl.inst_rf(x_fnl.regs[0] | x_fnl.h_regs[0], impl))
        res.discard(None)
        return res

    def terminates(self, impl: Implicant) -> Optional[RankFun]:
        assert isinstance(impl, Implicant)
        assert impl.env == self.fnls[0].env
        if not Funnel.get_use_ef() and not Funnel.get_use_motzkin():
            return None
        log("\tSeach ranking function for FLoop.",
            FLoop.get_log_lvl())
        # try to find rf proving termination of for outer loop,
        # assuming all inner ones terminate.
        # Notice that this rf has different constraints
        # from the ones inside the Funnels.
        env = impl.env
        delta = None
        if self.fnls[0].real_symbs:
            symbs = self.fnls[0].same_type_symbs
            expr, params = linear_comb(env, symbs)
            delta = new_param(env, "d", PyReal)
            params.add(delta)
            rf: RankFun = RRankFun(env, symbs, expr, delta, params)
        else:
            symbs = self.fnls[0].symbs
            expr, params = linear_comb(env, symbs)
            rf = IRankFun(env, symbs, expr, params)
        rf.canonize(impl.cn)
        if __debug__:  # check equivalence of constraints.
            mgr = env.formula_manager
            get_free_vars = env.fvo.get_free_variables
            ef_constrs = mgr.And(self._rf_constrs(rf))
            par_constrs = []
            motz_constrs = []
            for cube_it in self._rf_dnf(rf):
                cube = []
                for p in cube_it:
                    if get_free_vars(p) <= params:
                        par_constrs.append(p)
                    else:
                        cube.append(p)
                if len(cube) > 0:
                    motz_constrs.append(mgr.And(cube))
            motz_constrs = mgr.Not(mgr.Or(motz_constrs))
            if len(par_constrs) > 0:
                motz_constrs = mgr.And(mgr.And(par_constrs), motz_constrs)
            from solver import Solver
            with Solver(env=env) as _solver:
                # motz_constrs can be stronger.
                _solver.add_assertion(mgr.Not(mgr.Implies(motz_constrs,
                                                          ef_constrs)))
                assert _solver.solve() is False
            del ef_constrs, motz_constrs, par_constrs, mgr, _solver, get_free_vars
        # end debug.
        if Funnel.get_use_ef():
            log("\tUsing EF-solver.", FLoop.get_log_lvl())
            constr = env.formula_manager.And(
                self._rf_constrs(rf))
            model, _ = efmultisolve(env, params, None, constr, impl=impl)
        if model is None and Funnel.get_use_motzkin():
            log("\tUsing Motzkin transposition.", FLoop.get_log_lvl())
            model = motzkin_solve(env, params,
                                  self._rf_dnf(rf), self.fnls[0].cn.td,
                                  delta)
        if model is not None and model is not False:
            assert isinstance(model, dict)
            assert rf.params <= model.keys()
            return rf.instantiate(model)
        return None

    def instantiate(self, impl: Implicant) -> bool:
        assert isinstance(impl, Implicant)
        assert Funnel.get_use_ef() or Funnel.get_use_motzkin()
        if __debug__:  # check equivalence of constraints.
            motz_constrs = []
            par_constrs = []
            ef_constrs = []
            params = set()
            get_free_vars = impl.env.fvo.get_free_variables
            mgr = impl.env.formula_manager
            prev_fnl = self.fnls[0]
            for fnl in reversed(self.fnls):
                params.update(fnl.params)
                ef_constrs.extend(fnl.constrs(prev_fnl.first(),
                                              prev_fnl.h_first()))
                for cube_it in fnl.dnf_constrs(prev_fnl.first(),
                                               prev_fnl.h_first()):
                    cube = []
                    for p in cube_it:
                        if get_free_vars(p) <= params:
                            par_constrs.append(p)
                        else:
                            cube.append(p)
                    if len(cube) > 0:
                        motz_constrs.append(mgr.And(cube))
                prev_fnl = fnl
            ef_constrs = mgr.And(ef_constrs)
            motz_constrs = mgr.Not(mgr.Or(motz_constrs))
            if len(par_constrs) > 0:
                motz_constrs = mgr.And(mgr.And(par_constrs), motz_constrs)
            from solver import Solver
            with Solver(env=impl.env) as _solver:
                _solver.add_assertion(mgr.Not(mgr.Iff(motz_constrs, ef_constrs)))
                assert _solver.solve() is False
            del (ef_constrs, prev_fnl, motz_constrs, par_constrs, _solver, mgr,
                 get_free_vars, params)
        # end debug.
        env = impl.env
        simpl = env.simplifier.simplify
        subst = env.substituter.substitute
        ffnl = self.fnls[0]
        first_constr = list(filter(lambda p: not p.is_true(),
                                   (simpl(subst(p, self.first_state))
                                    for p in chain(ffnl.first(),
                                                   ffnl.h_first()))))
        model = None
        log("\tTry synthesise FLoop from candidate.", FLoop.get_log_lvl())
        if Funnel.get_use_ef():
            log("\tUsing EF-solver.", FLoop.get_log_lvl())
            mgr = env.formula_manager
            params: Set[FNode] = set()
            prev_fnl = ffnl
            constrs = first_constr.copy()
            for fnl in reversed(self.fnls):
                constrs.extend(fnl.constrs(prev_fnl.first(),
                                           prev_fnl.h_first()))
                params.update(fnl.params)
                prev_fnl = fnl
            model, _ = efmultisolve(env, params, None, mgr.And(constrs),
                                    impl=impl)
        if model is None and Funnel.get_use_motzkin():
            log("\tUsing Motzkin-transposition.", FLoop.get_log_lvl())
            dnf_constrs = [first_constr]
            del first_constr
            params = set()
            prev_fnl = ffnl
            for fnl in reversed(self.fnls):
                dnf_constrs.extend(fnl.dnf_constrs(prev_fnl.first(),
                                                   prev_fnl.h_first()))
                params.update(fnl.params)
                prev_fnl = fnl
            model = motzkin_solve(env, params, dnf_constrs, self.fnls[0].cn.td)
        if model is not None and model is not False:
            assert isinstance(model, dict)
            assert all(fnl.params <= model.keys() for fnl in self.fnls)
            assert all(simpl(subst(subst(p, self.first_state), model)).is_true()
                       for p in chain(self.fnls[0].first(),
                                      self.fnls[0].h_first()))
            for fnl in self.fnls:
                fnl.instantiate(model)
            return True
        return False

    def _rf_constrs(self, rf: RankFun) -> Iterator[FNode]:
        """Return constraints such that:
        rf does not increase in every sub-path and
        there exists a sub-path in which it decreases."""
        env = self.fnls[0].env
        mgr = env.formula_manager
        totime = self.fnls[0].totime
        yield from rf.param_constrs()
        if len(self.fnls) == 1 and not isinstance(self.fnls[0], RFFunnel):
            # single non-ranked Funnel.
            assert isinstance(self.fnls[0], Funnel)
            fnl = self.fnls[0]
            last = len(fnl)
            assert len(list(fnl.exit_path(False))) == last + 1
            path = list(totime(p, t)
                        for t, step in enumerate(fnl.exit_path(False))
                        for p in step)
            assert len(list(list(fnl.exit_path(False))[-1])) == 0
            path.extend(totime(p, last)
                        for p in chain(fnl.regs[0], fnl.h_regs[0]))
            # path -> rf > 0 & rf' < rf
            yield mgr.Implies(mgr.And(path),
                              mgr.And(totime(rf.is_ranked(), 0),
                                      totime(rf.is_decr(), 0, last)))
            return
        not_incr = mgr.LE(rf.x_expr, rf.expr)
        # (/\ lhs) -> (/\ leqs) & (\/ lts) & (\/ gts)
        lhs: List[FNode] = []  # list of paths.
        leqs: List[FNode] = []  # rf does not increase in each path.
        lts: List[FNode] = []  # rf decreases in at least 1 path.
        gts: List[FNode] = []  # at least 1 path implies rf > 0.
        start_t = 0
        idx = 0
        while idx < len(self.fnls):
            fnl = self.fnls[idx]
            assert isinstance(fnl, RFFunnel)
            assert len(lhs) == 0 or all(t < start_t for pred in lhs
                                        for t in get_times(env, pred))
            curr_t = start_t
            # Yield rffnl.loop-path -> rf' <= rf
            lpath = list(fnl.loop_path(False))
            yield mgr.Implies(
                mgr.And(totime(p, t) for t, preds in enumerate(lpath,
                                                               start=curr_t)
                        for p in preds),
                totime(not_incr, curr_t, curr_t + len(lpath) - 1))
            assert all(_t <= curr_t + len(lpath) - 1
                       for t, preds in enumerate(fnl.loop_path(False),
                                                 start=curr_t)
                       for p in preds
                       for _t in get_times(env, totime(p, t)))
            assert any(_t == curr_t + len(lpath) - 1
                       for t, preds in enumerate(fnl.loop_path(False),
                                                 start=curr_t)
                       for p in preds
                       for _t in get_times(env, totime(p, t)))

            # Exit from first RFFunnel.
            for curr_t, preds in enumerate(fnl.exit_path(False),
                                           start=start_t):
                lhs.extend(totime(p, curr_t) for p in preds)
            assert all(t <= curr_t
                       for pred in lhs for t in get_times(env, pred))
            assert any(t == curr_t
                       for pred in lhs for t in get_times(env, pred))
            idx += 1
            fnl = self.fnls[idx % len(self.fnls)]

            if not isinstance(fnl, RFFunnel):
                # Path of non-ranked Funnel.
                for curr_t, preds in enumerate(fnl.exit_path(False),
                                               start=curr_t):
                    lhs.extend(totime(p, curr_t) for p in preds)
                assert all(t <= curr_t
                           for pred in lhs for t in get_times(env, pred))
                assert any(t == curr_t
                           for pred in lhs for t in get_times(env, pred))
                idx += 1
                fnl = self.fnls[idx % len(self.fnls)]

            # Enter in following RFFunnel.
            assert isinstance(fnl, RFFunnel)
            for curr_t, preds in enumerate(fnl.enter_path(False),
                                           start=curr_t):
                lhs.extend(totime(p, curr_t) for p in preds)
            leqs.append(totime(not_incr, start_t, curr_t))
            lts.append(totime(rf.is_decr(), start_t, curr_t))
            gts.append(totime(rf.is_ranked(), start_t))
            assert all(t <= curr_t
                       for pred in lhs for t in get_times(env, pred))
            assert any(t == curr_t
                       for pred in lhs for t in get_times(env, pred))
            assert all(t <= curr_t
                       for pred in leqs for t in get_times(env, pred))
            assert any(t == curr_t
                       for pred in leqs for t in get_times(env, pred))
            assert all(t <= curr_t
                       for pred in lts for t in get_times(env, pred))
            assert any(t == curr_t
                       for pred in lts for t in get_times(env, pred))
            assert all(t <= start_t
                       for pred in gts for t in get_times(env, pred))
            assert all(t == start_t for t in get_times(env, gts[-1]))
            start_t = curr_t + 1
        assert len(lhs) > 1
        yield mgr.Implies(mgr.And(lhs), mgr.And(mgr.And(leqs), mgr.Or(lts),
                                                mgr.Or(gts)))

    def _rf_dnf(self, rf: RankFun) -> Iterator[Iterator[FNode]]:
        """Return negation of constraints in DNF"""
        env = self.fnls[0].env
        mgr = env.formula_manager
        totime = self.fnls[0].totime
        par_constrs = list(rf.param_constrs())
        if len(par_constrs) > 0:
            yield par_constrs
        not_decr = not_rel(env, rf.is_decr())
        if len(self.fnls) == 1 and not isinstance(self.fnls[0], RFFunnel):
            # single non-ranked Funnel.
            assert isinstance(self.fnls[0], Funnel)
            fnl = self.fnls[0]
            last = len(fnl)
            assert len(list(fnl.exit_path(False))) == last + 1
            path = list(totime(p, t)
                        for t, step in enumerate(fnl.exit_path(False))
                        for p in step)
            path.extend(totime(p, last)
                        for p in chain(fnl.regs[0], fnl.h_regs[0]))
            yield chain(path, [totime(rf.is_min(), 0)])
            yield chain(path, [totime(not_decr, 0, last)])
            return
        # for all paths: (path -> rf' <= rf) --> E-path: (path & rf' > rf)
        # for some path: path -> rf' < rf --> /\ paths & /\ rf' >= rf;
        # for some path: path -> rf > 0 --> /\ paths & /\ rf <= 0.
        incr = mgr.GT(rf.x_expr, rf.expr)
        paths: List[FNode] = []
        geqs: List[FNode] = []
        leqs: List[FNode] = []
        start_t = 0
        idx = 0
        while idx < len(self.fnls):
            fnl = self.fnls[idx]
            assert isinstance(fnl, RFFunnel)
            assert len(paths) == 0 or all(t < start_t for pred in paths
                                          for t in get_times(env, pred))
            assert len(geqs) == 0 or all(t < start_t for pred in geqs
                                         for t in get_times(env, pred))
            assert len(leqs) == 0 or all(t < start_t for pred in leqs
                                         for t in get_times(env, pred))
            curr_t = start_t
            # Yield !(rffnl.loop-path -> rf' <= rf)
            lpath = list(fnl.loop_path(False))
            yield chain((totime(p, t)
                         for t, preds in enumerate(lpath, start=curr_t)
                         for p in preds),
                        [totime(incr, curr_t, curr_t + len(lpath) - 1)])
            assert all(_t <= curr_t + len(lpath) - 1
                       for t, preds in enumerate(fnl.loop_path(False),
                                                 start=curr_t)
                       for p in preds
                       for _t in get_times(env, totime(p, t)))
            assert any(_t == curr_t + len(lpath) - 1
                       for t, preds in enumerate(fnl.loop_path(False),
                                                 start=curr_t)
                       for p in preds
                       for _t in get_times(env, totime(p, t)))
            curr_path: List[FNode] = []
            # Exit from first RFFunnel.
            for curr_t, preds in enumerate(fnl.exit_path(False),
                                           start=start_t):
                curr_path.extend(totime(p, curr_t) for p in preds)
            assert all(t <= curr_t for pred in curr_path
                       for t in get_times(env, pred))
            assert any(t == curr_t for pred in curr_path
                       for t in get_times(env, pred))
            idx += 1
            fnl = self.fnls[idx % len(self.fnls)]

            if not isinstance(fnl, RFFunnel):
                # Path of non-ranked Funnel.
                for curr_t, preds in enumerate(fnl.exit_path(False),
                                               start=curr_t):
                    curr_path.extend(totime(p, curr_t) for p in preds)
                assert all(t <= curr_t for pred in curr_path
                           for t in get_times(env, pred))
                assert any(t == curr_t for pred in curr_path
                           for t in get_times(env, pred))
                idx += 1
                fnl = self.fnls[idx % len(self.fnls)]

            # Enter in following RFFunnel.
            assert isinstance(fnl, RFFunnel)
            for curr_t, preds in enumerate(fnl.enter_path(False),
                                           start=curr_t):
                curr_path.extend(totime(p, curr_t) for p in preds)
            assert all(start_t <= t for pred in curr_path
                       for t in get_times(env, pred))
            assert any(t == start_t for pred in curr_path
                       for t in get_times(env, pred))
            assert all(t <= curr_t for pred in curr_path
                       for t in get_times(env, pred))
            assert any(t == curr_t for pred in curr_path
                       for t in get_times(env, pred))
            # yield !(curr_path -> rf' <= rf)
            yield chain(curr_path, [totime(incr, start_t, curr_t)])
            paths.extend(curr_path)
            geqs.append(totime(not_decr, start_t, curr_t))
            leqs.append(totime(rf.is_min(), start_t))
            assert all(t <= curr_t for pred in paths
                       for t in get_times(env, pred))
            assert any(t == curr_t for pred in paths
                       for t in get_times(env, pred))
            assert all(t <= curr_t for pred in geqs
                       for t in get_times(env, pred))
            assert any(t == curr_t for pred in geqs
                       for t in get_times(env, pred))
            assert all(t <= start_t for pred in leqs
                       for t in get_times(env, pred))
            assert all(t == start_t for t in get_times(env, leqs[-1]))
            start_t = curr_t + 1  # start fresh path in next iteration.
        yield chain(paths, geqs)
        yield chain(paths, leqs)
