from __future__ import annotations
from typing import FrozenSet, Optional

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
from pysmt.typing import PySMTType

from utils import to_next


class RankFun():
    """Represents a ranking function.
    `expr` that can decrease of `delta` a finite number of times before
    becoming negative"""
    def __init__(self, env: PysmtEnv,
                 expr: FNode, delta: FNode,
                 symbols: FrozenSet[FNode],
                 params: Optional[FrozenSet[FNode]] = None):
        # TODO: "optimise" special case of integer-type expr.
        assert isinstance(env, PysmtEnv)
        assert isinstance(expr, FNode)
        assert isinstance(delta, FNode)
        assert env.stc.get_type(expr) == env.stc.get_type(delta)
        assert env.stc.get_type(delta).is_int_type() or \
            env.stc.get_type(delta).is_real_type()
        assert expr in env.formula_manager.formulae.values()
        assert delta in env.formula_manager.formulae.values()
        assert isinstance(symbols, frozenset)
        assert params is None or isinstance(params, frozenset)
        assert all(isinstance(s, FNode) for s in symbols)
        assert params is None or all(isinstance(s, FNode) for s in params)
        assert all(s in env.formula_manager.get_all_symbols() or
                   (s.is_toreal() and
                    s.arg(0) in env.formula_manager.get_all_symbols())
                   for s in symbols)
        assert params is None or all(s in env.formula_manager.get_all_symbols()
                                     for s in params)

        self.env = env
        self.expr = expr
        self.delta = delta
        self.symbols = symbols
        self._leaf_symbs = frozenset(s.arg(0) if s.is_toreal() else s
                                     for s in self.symbols)
        assert all(s.is_symbol() for s in self._leaf_symbs)
        self.rf_type = env.stc.get_type(delta)
        self.params = params if params is not None else frozenset()

    def constant_pred(self) -> FNode:
        """Return formula which is true iff rf' = rf"""
        mgr = self.env.formula_manager
        x_expr = to_next(mgr, self.expr, self._leaf_symbs)
        return mgr.Equals(x_expr, self.expr)

    def decrease_pred(self) -> FNode:
        """Return formula which is true iff rf' < rf"""
        mgr = self.env.formula_manager
        x_expr = to_next(mgr, self.expr, self._leaf_symbs)
        return mgr.LE(x_expr, mgr.Minus(self.expr, self.delta))

    def progress_pred(self) -> FNode:
        """Return formula which is true if curr-next pair is ranked"""
        return self.env.formula_manager.And(self.is_ranked,
                                            self.decrease_pred())

    @property
    def min_el(self) -> FNode:
        mgr = self.env.formula_manager
        if self.rf_type.is_real_type():
            return mgr.Real(0)
        assert self.rf_type.is_int_type()
        return mgr.Int(0)

    @property
    def is_ranked(self) -> FNode:
        return self.env.formula_manager.GT(self.expr, self.min_el)

    def instantiate(self, model) -> RankFun:
        assert all(k not in self.symbols for k in model.keys())
        assert all(p in model.keys() for p in self.params)

        subst = self.env.substituter.substitute

        return RankFun(self.env, subst(self.expr, model),
                       subst(self.delta, model),
                       self.symbols)

    def to_env(self, new_env: PysmtEnv) -> RankFun:
        """Return copy of self in the give environment"""
        assert isinstance(new_env, PysmtEnv)

        norm = new_env.formula_manager.normalize
        return RankFun(new_env, norm(self.expr), norm(self.delta),
                       frozenset(norm(s) for s in self.symbols),
                       frozenset(norm(p) for p in self.params))

    def __eq__(self, other) -> bool:
        if not isinstance(other, self.__class__):
            return False
        if self.env != other.env or self.rf_type != other.rf_type:
            return False
        return self.delta == other.delta and self.expr == other.expr

    def __hash__(self):
        return hash((self.expr, self.delta))

    def __str__(self) -> str:
        serialize = self.env.serializer.serialize
        return f"({serialize(self.expr)} > {serialize(self.min_el)}; {serialize(self.delta)})"
