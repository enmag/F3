from typing import Optional, Tuple, Dict
from collections import defaultdict

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
from pysmt.walkers import IdentityDagWalker

from expr_utils import (name2timed, get_name_time,
                        name2next, name2curr, name_is_next)


class ExprAtTime(IdentityDagWalker):
    """Rewrite symbols in the s@time version and vice-versa"""

    def __init__(self, env: PysmtEnv, idx: int = 0,
                 x_idx: Optional[int] = None):
        assert isinstance(env, PysmtEnv)
        assert isinstance(idx, int)
        assert x_idx is None or isinstance(x_idx, int)
        super().__init__(env=env)
        self.dict_cache: Dict[Tuple[int, Optional[int]],
                              Dict[FNode, FNode]] = defaultdict(dict)
        self._set_time(idx, x_idx)
        assert self._idx is not None
        assert self._x_idx is not None

    def _set_time(self, idx: int, x_idx: Optional[int] = None) -> None:
        assert isinstance(idx, int)
        assert x_idx is None or isinstance(x_idx, int)
        assert isinstance(self.memoization, dict)
        self._idx = idx
        if x_idx is not None:
            self._x_idx = x_idx
        elif self._idx >= 0:
            self._x_idx = idx + 1
        else:
            self._x_idx = idx - 1

        assert self._idx < 0 or self._x_idx >= 0
        assert self._idx >= 0 or self._x_idx < 0
        # override superclass
        self.memoization = self.dict_cache[(self._idx, self._x_idx)]
        self.handle_symb = self.symb2timed if self._idx >= 0 \
            else self.symb2untimed

    def symb2timed(self, s: FNode) -> FNode:
        assert isinstance(s, FNode)
        assert s.is_symbol()
        assert s in self.env.formula_manager.get_all_symbols()
        assert self._idx >= 0
        name = s.symbol_name()
        t = self._idx
        if name_is_next(name):
            t = self._x_idx
            name = name2curr(name)
        name = name2timed(name, t)
        return self.env.formula_manager.Symbol(name, s.symbol_type())

    def symb2untimed(self, s: FNode) -> FNode:
        assert isinstance(s, FNode)
        assert s.is_symbol()
        assert s in self.env.formula_manager.get_all_symbols()
        assert self._idx < 0
        assert not name_is_next(s.symbol_name())
        name, num = get_name_time(s.symbol_name())
        if num is not None:
            assert num in {-self._idx - 1, -self._x_idx - 1}
            if num == -self._x_idx - 1:
                name = name2next(name)
            return self.env.formula_manager.Symbol(name, s.symbol_type())
        return s

    def walk_symbol(self, fm: FNode, **_) -> FNode:
        return self.handle_symb(fm)

    def walk(self, formula: FNode, idx: int,
             x_idx: Optional[int] = None) -> FNode:
        assert isinstance(formula, FNode)
        assert isinstance(idx, int)
        assert x_idx is None or isinstance(x_idx, int)
        self._set_time(idx, x_idx=x_idx)
        return IdentityDagWalker.walk(self, formula)

    def __call__(self, formula: FNode, idx: int,
                 x_idx: Optional[int] = None) -> FNode:
        return self.walk(formula, idx, x_idx=x_idx)
