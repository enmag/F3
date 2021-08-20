from typing import Tuple, Optional
from collections import defaultdict

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
from pysmt.formula import FormulaManager
from pysmt.walkers import IdentityDagWalker

from utils import name_is_next, name_next, name_next_to_curr


class ExprAtTime(IdentityDagWalker):
    """Rewrite each symbol in the s@time version"""

    @staticmethod
    def collect_times(mgr: FormulaManager, formula: FNode) -> set:
        assert isinstance(mgr, FormulaManager)
        assert isinstance(formula, FNode)
        assert formula in mgr.formulae.values()
        res = set()
        for v in mgr.env.fvo.walk(formula):
            if "@" in v.symbol_name():
                _, num = ExprAtTime.get_symb_time(mgr, v)
                res.add(num)
        return res

    @staticmethod
    def is_timed_symb(mgr: FormulaManager, s: FNode) -> bool:
        assert isinstance(mgr, FormulaManager)
        assert isinstance(s, FNode)
        assert s in mgr.formulae.values()
        return "@" in s.symbol_name()

    @staticmethod
    def get_symb_time(mgr: FormulaManager, s: FNode) -> Tuple[str, int]:
        assert isinstance(mgr, FormulaManager)
        assert isinstance(s, FNode)
        assert s.is_symbol(), s
        assert "@" in s.symbol_name()
        symb_name = s.symbol_name()
        idx = symb_name.find("@")
        name = symb_name[:idx]
        num = int(symb_name[idx+1:])
        return name, num

    @staticmethod
    def symb_untime(mgr: FormulaManager, s: FNode) -> FNode:
        assert isinstance(mgr, FormulaManager)
        assert isinstance(s, FNode)
        assert s.is_symbol()
        symb_name = s.symbol_name()
        if "@" in s.symbol_name():
            symb_name, _ = ExprAtTime.get_symb_time(mgr, s)
        return mgr.Symbol(symb_name, s.symbol_type())

    def __init__(self, env: PysmtEnv = None, idx: int = 0, x_idx: int = 1,
                 ignore_pref: Optional[str] = None):
        assert env is None or isinstance(env, PysmtEnv)
        assert isinstance(idx, int)
        assert isinstance(x_idx, int)
        assert ignore_pref is None or isinstance(ignore_pref, str)
        IdentityDagWalker.__init__(self, env)
        self.mgr = self.env.formula_manager
        self.idx = idx
        self.x_idx = x_idx
        self.ignore_pref = ignore_pref
        self.dict_mem = defaultdict(dict)
        self.memoization = self.dict_mem[(self.idx, self.x_idx)]

    def _set_time(self, idx: int, x_idx: Optional[int] = None) -> None:
        assert isinstance(idx, int)
        assert x_idx is None or isinstance(x_idx, int)
        assert isinstance(self.memoization, dict)
        self.idx = idx
        if x_idx is not None:
            self.x_idx = x_idx
        elif self.idx >= 0:
            self.x_idx = idx + 1
        else:
            self.x_idx = idx - 1

        assert self.idx < 0 or self.x_idx >= 0
        assert self.idx >= 0 or self.x_idx < 0

        self.memoization = self.dict_mem[(idx, x_idx)]

    def _at_time(self, s: FNode) -> FNode:
        assert isinstance(s, FNode)
        assert s.is_symbol()
        assert "@" not in s.symbol_name() or self.idx < 0
        symb_name = s.symbol_name()
        if self.ignore_pref and symb_name.startswith(self.ignore_pref):
            return self.mgr.Symbol(symb_name, s.symbol_type())

        idx = self.idx
        if name_is_next(symb_name):
            assert (self.idx >= 0 and self.x_idx >= 0) or self.x_idx < self.idx
            idx = self.x_idx
            symb_name = name_next_to_curr(symb_name)

        name = None
        if idx < 0:
            assert self.x_idx < 0
            name, num = ExprAtTime.get_symb_time(self.mgr, s)
            assert num in {-idx - 1, -self.x_idx - 1}
            if num == -self.x_idx - 1:
                name = name_next(name)
        else:
            name = f"{symb_name}@{idx}"

        return self.mgr.Symbol(name, s.symbol_type())

    def walk(self, formula: FNode, idx: int, x_idx: Optional[int] = None,
             **kwargs) -> FNode:
        assert isinstance(formula, FNode)
        assert isinstance(idx, int)
        assert x_idx is None or isinstance(x_idx, int)
        self._set_time(idx, x_idx=x_idx)
        return IdentityDagWalker.walk(self, formula, **kwargs)

    def __call__(self, formula: FNode, idx: int, x_idx: Optional[int] = None,
                 **kwargs):
        return self.walk(formula, idx, x_idx=x_idx, **kwargs)

    def walk_symbol(self, formula: FNode, args, **kwargs):
        return self._at_time(formula)
