from __future__ import annotations
from typing import FrozenSet, Iterable, Iterator, Union
from itertools import chain

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode

from smv_printer import SMVPrinter
from expr_utils import symb_is_curr, flatten


class TransSystem:
    """Represent a transition system:
    <symbols, initials, transition relation>"""

    def __init__(self, env: PysmtEnv, symbs: FrozenSet[FNode],
                 init: Union[FNode, Iterable[FNode], Iterator[FNode]],
                 trans: Union[FNode, Iterable[FNode], Iterator[FNode]]):
        assert isinstance(env, PysmtEnv)
        assert isinstance(symbs, frozenset)
        assert all(isinstance(s, FNode) for s in symbs)
        assert all(s.is_symbol() for s in symbs)
        assert all(s in env.formula_manager.get_all_symbols() for s in symbs)
        assert all(symb_is_curr(s) for s in symbs)
        self.env = env
        self._symbs = set(symbs)
        self._init = set(p for p in flatten(init, lambda x: x.is_and()))
        self._trans = set(p for p in flatten(trans, lambda x: x.is_and()))
        assert not init or self._init
        assert not trans or self._trans
        assert all(pred in env.formula_manager.formulae.values()
                   for pred in self.init)
        assert all(pred in env.formula_manager.formulae.values()
                   for pred in self.trans)

    @property
    def symbs(self) -> FrozenSet[FNode]:
        assert isinstance(self._symbs, (set, frozenset))
        assert all(isinstance(s, FNode) for s in self._symbs)
        assert all(s in self.env.formula_manager.get_all_symbols()
                   for s in self._symbs)
        return frozenset(self._symbs)

    @property
    def init(self) -> FrozenSet[FNode]:
        assert isinstance(self._init, (set, frozenset))
        assert all(isinstance(p, FNode) for p in self._init)
        return frozenset(self._init)

    @property
    def trans(self) -> FrozenSet[FNode]:
        assert isinstance(self._trans, (set, frozenset))
        assert all(isinstance(p, FNode) for p in self._trans)
        return frozenset(self._trans)

    def add_symb(self, s: FNode) -> None:
        assert isinstance(s, FNode)
        assert s in self.env.formula_manager.get_all_symbols()
        self._symbs.add(s)

    def ext_symbs(self, new_symbs: Union[Iterable[FNode],
                                         Iterator[FNode]]) -> None:
        self._symbs.update(new_symbs)
        assert all(isinstance(s, FNode) for s in self.symbs)
        assert all(s in self.env.formula_manager.get_all_symbols()
                   for s in self.symbs)

    def add_init(self, pred: FNode):
        assert self.env.fvo.get_free_variables(pred) <= self.symbs
        self._init.update(flatten(pred, lambda x: x.is_and()))

    def ext_init(self, preds: Union[FNode, Iterable[FNode], Iterator[FNode]]):
        self._init.update(flatten(preds, lambda x: x.is_and()))

    def add_trans(self, pred: FNode):
        self._trans.update(flatten(pred, lambda x: x.is_and()))

    def ext_trans(self, preds: Union[FNode, Iterable[FNode], Iterator[FNode]]):
        self._trans.update(flatten(preds, lambda x: x.is_and()))

    def to_env(self, o_env: PysmtEnv) -> TransSystem:
        assert isinstance(o_env, PysmtEnv)
        o_norm = o_env.normalizer.normalize
        return TransSystem(o_env, frozenset(o_norm(s) for s in self.symbs),
                           [o_norm(pred) for pred in self.init],
                           [o_norm(pred) for pred in self.trans])

    def prods(self, lst: Iterable[TransSystem]) -> None:
        assert isinstance(lst, (list, set, frozenset, tuple))
        assert all(isinstance(o, TransSystem) for o in lst)
        self.ext_symbs(chain.from_iterable(ts.symbs for ts in lst))
        self.ext_init(chain.from_iterable(ts.init for ts in lst))
        self.ext_trans(chain.from_iterable(ts.trans for ts in lst))

    def prod(self, o: TransSystem) -> None:
        assert o.env == self.env
        assert isinstance(o, TransSystem)
        self.ext_symbs(o.symbs)
        self.ext_init(o.init)
        self.ext_trans(o.trans)

    def to_smv(self, printer: SMVPrinter, name: str = "main") -> None:
        assert isinstance(printer, SMVPrinter)
        assert isinstance(name, str)
        printer.write_module(name)
        printer.decl_symbs(self.symbs)
        for pred in self.init:
            printer.write_init(pred)
        for pred in self.trans:
            printer.write_trans(pred)
