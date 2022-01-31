from __future__ import annotations
from typing import Iterator, FrozenSet, Set, Union, Dict

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
from pysmt.typing import PySMTType

from canonize import Canonizer
from expr_utils import to_next


class RankFun():
    """Represents a ranking function.
    `expr` can decrease a finite number of times before becoming negative.
    This is a virtual class."""

    def __init__(self, env: PysmtEnv,
                 symbs: FrozenSet[FNode],
                 expr: FNode,
                 params: Union[Set[FNode], FrozenSet[FNode]]):
        assert isinstance(env, PysmtEnv)
        assert isinstance(symbs, frozenset)
        assert all(isinstance(s, FNode) for s in symbs)
        assert all(s.is_symbol() or s.is_toreal() for s in symbs)
        assert all(s.is_symbol() or s.arg(0).is_symbol() for s in symbs)
        assert all(s in env.formula_manager.formulae.values() for s in symbs)
        assert all(env.stc.get_type(s).is_int_type() for s in symbs) or \
            all(env.stc.get_type(s).is_real_type() for s in symbs)
        assert isinstance(expr, FNode)
        assert expr in env.formula_manager.formulae.values()
        assert all(v in frozenset(s if s.is_symbol() else s.arg(0)
                                  for s in symbs) or
                   v in params
                   for v in env.fvo.get_free_variables(expr))
        assert isinstance(params, (set, frozenset))
        assert all(isinstance(p, FNode) for p in params)
        assert all(p.is_symbol() for p in params)
        assert all(p in env.formula_manager.get_all_symbols()
                   for p in params)
        assert len(params & symbs) == 0
        self.env = env
        self.symbs = symbs
        self._expr = expr
        self._x_expr = to_next(env, expr,
                               frozenset(s if s.is_symbol() else s.arg(0)
                                         for s in symbs))
        self.params = frozenset(params)
        self._is_constant = env.formula_manager.Equals(self.expr, self.x_expr)

    @property
    def expr(self) -> FNode:
        """Return expression representing the rankfun"""
        return self._expr

    @property
    def x_expr(self) -> FNode:
        """Return expression representing the rankfun at next step"""
        return self._x_expr

    @property
    def min_el(self) -> FNode:
        """Return constant representing min_el of rankfun"""
        return self._min_el

    def is_ranked(self) -> FNode:
        return self._is_ranked

    def is_min(self) -> FNode:
        """Return negation of is_ranked"""
        return self._is_min

    def is_const(self) -> FNode:
        """Return formula that holds iff rankfun remains constant"""
        return self._is_constant

    def is_decr(self) -> FNode:
        """Return formula that holds iff rankfun decreases"""
        return self._is_decr

    def is_trivial(self) -> bool:
        """Return True iff the ranking function either always or never holds"""
        return self.env.simplifier.simplify(self.is_decr()).is_bool_constant()

    def instantiate(self, _) -> RankFun:
        """Return new RankFun where all parameters have been replaced
        as described by the given `model`"""
        assert False, "RankFun is virtual"

    def to_env(self, _) -> RankFun:
        """Return same RankFun in given environment"""
        assert False, "RankFun is virtual"

    def param_constrs(self) -> Iterator[FNode]:
        """Return constraints over the parameters"""
        assert False, "RankFun is virtual"
        return []

    def canonize(self, cn: Canonizer) -> None:
        assert isinstance(cn, Canonizer)
        assert cn.env == self.env
        self._expr = cn(self.expr)
        self._x_expr = cn(self.x_expr)
        self._is_constant = cn(self.is_const())
        self._is_ranked = cn(self.is_ranked())
        self._is_min = cn(self.is_min())
        self._is_decr = cn(self.is_decr())

    def mk_symbs_constant(self, assign: Dict[FNode, FNode]) -> None:
        simpl = self.env.simplifier.simplfy
        subst = self.env.substituter.substitute
        self.symbs -= assign
        self._expr = simpl(subst(self.expr, assign))
        self._x_expr = to_next(self.env, self.expr,
                               frozenset(s if s.is_symbol() else s.arg(0)
                                         for s in self.symbs))
        self._is_constant = self.env.formula_manager.Equals(self.expr,
                                                            self.x_expr)

class RRankFun(RankFun):
    """Represents a real-valued ranking function.
    `expr` decreases of `delta` at each step."""

    def __init__(self, env: PysmtEnv,
                 symbs: FrozenSet[FNode],
                 expr: FNode, delta: FNode,
                 params: Union[Set[FNode], FrozenSet[FNode]]):
        assert env.stc.get_type(expr).is_real_type()
        assert isinstance(delta, FNode)
        assert env.stc.get_type(delta).is_real_type()
        assert delta.is_constant() or delta in params
        assert delta in env.formula_manager.formulae.values()

        super().__init__(env, symbs, expr, params)
        mgr = self.env.formula_manager
        self.delta = delta
        self._min_el = mgr.Real(0)
        self._is_ranked = mgr.GT(self.expr, self.min_el)
        self._is_min = mgr.LE(self.expr, self.min_el)
        self._is_decr = mgr.LE(mgr.Plus(self.x_expr, delta), self.expr)

    def mk_symbs_constant(self, assign: Dict[FNode, FNode]) -> None:
        super().mk_symbs_constant(assign)
        mgr = self.env.formula_manager
        self._is_ranked = mgr.GT(self.expr, self.min_el)
        self._is_min = mgr.LE(self.expr, self.min_el)
        self._is_decr = mgr.LE(mgr.Plus(self.x_expr, self.delta), self.expr)

    def instantiate(self, model) -> RRankFun:
        assert all(k not in self.symbs for k in model.keys())
        assert all(p in model.keys() for p in self.params)

        subst = self.env.substituter.substitute
        return RRankFun(self.env, self.symbs,
                        subst(self.expr, model),
                        subst(self.delta, model),
                        frozenset())

    def to_env(self, env: PysmtEnv) -> RRankFun:
        assert isinstance(env, PysmtEnv)

        norm = env.formula_manager.normalize
        return RRankFun(env, frozenset(norm(s) for s in self.symbs),
                        norm(self.expr), norm(self.delta),
                        frozenset(norm(p) for p in self.params))

    def param_constrs(self) -> Iterator[FNode]:
        if self.params:
            mgr = self.env.formula_manager
            yield mgr.LT(mgr.Real(0), self.delta)
        return []

    def __eq__(self, other) -> bool:
        if not isinstance(other, self.__class__):
            return False
        if self.env != other.env:
            return False
        return self.delta == other.delta and self.expr == other.expr

    def __hash__(self):
        return hash((self.expr, self.delta))

    def __str__(self) -> str:
        serialize = self.env.serializer.serialize
        return f"Rf: <{serialize(self.expr)}; {serialize(self.delta)}>"


class IRankFun(RankFun):
    """Represents a int-valued ranking function.
    `expr` decreases of at least 1 each step."""

    def __init__(self, env: PysmtEnv,
                 symbs: FrozenSet[FNode],
                 expr: FNode,
                 params: Union[Set[FNode], FrozenSet[FNode]]):
        assert env.stc.get_type(expr).is_int_type()

        super().__init__(env, symbs, expr, params)
        mgr = self.env.formula_manager
        self._min_el = mgr.Int(0)
        self._is_ranked = mgr.GT(self.expr, self.min_el)
        self._is_min = mgr.LE(self.expr, self.min_el)
        self._is_decr = mgr.LT(self.x_expr, self.expr)

    def mk_symbs_constant(self, assign: Dict[FNode, FNode]) -> None:
        super().mk_symbs_constant(assign)
        mgr = self.env.formula_manager
        self._is_ranked = mgr.GT(self.expr, self.min_el)
        self._is_min = mgr.LE(self.expr, self.min_el)
        self._is_decr = mgr.LT(self.x_expr, self.expr)

    def instantiate(self, model) -> IRankFun:
        assert all(k not in self.symbs for k in model.keys())
        assert all(p in model.keys() for p in self.params)

        subst = self.env.substituter.substitute
        return IRankFun(self.env, self.symbs,
                        subst(self.expr, model),
                        frozenset())

    def param_constrs(self) -> Iterator[FNode]:
        return []

    def to_env(self, env: PysmtEnv) -> IRankFun:
        assert isinstance(env, PysmtEnv)

        norm = env.formula_manager.normalize
        return IRankFun(env, frozenset(norm(s) for s in self.symbs),
                        norm(self.expr),
                        frozenset(norm(p) for p in self.params))

    def __eq__(self, other) -> bool:
        if not isinstance(other, self.__class__):
            return False
        if self.env != other.env:
            return False
        return self.expr == other.expr

    def __hash__(self):
        return hash(self.expr)

    def __str__(self) -> str:
        serialize = self.env.serializer.serialize
        return f"Rf: <{serialize(self.expr)}; 1>"
