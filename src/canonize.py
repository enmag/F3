from typing import Iterator, Iterable, Optional

from pysmt.environment import Environment as PysmtEnv
from pysmt.walkers import IdentityDagWalker
from pysmt.fnode import FNode

from ineq import Ineq
from rewritings import TimesDistributor
from utils import default_key


class Canonizer(IdentityDagWalker):
    """Rearrange ordering for commutative expressions to increase sharing

    Does not increase depth of the tree representing the formula.
    """

    def __init__(self, key=None, env: PysmtEnv = None,
                 inv_mem: Optional[bool] = None):
        assert isinstance(env, PysmtEnv)
        assert inv_mem is None or isinstance(inv_mem, bool)
        IdentityDagWalker.__init__(self, env=env,
                                   invalidate_memoization=inv_mem)
        if not key:
            key = default_key
        self._key = key
        self.td = TimesDistributor(env=self.env)

    def _sort(self, args: Iterable[FNode]):
        assert isinstance(args, Iterable)
        return sorted(args, key=self._key)

    def __call__(self, formula: FNode, **kwargs):
        return self.walk(formula, **kwargs)

    if __debug__:
        def walk(self, formula: FNode, **kwargs) -> FNode:
            assert formula in self.env.formula_manager.formulae.values()
            res = super().walk(formula, **kwargs)
            from solver import Solver
            mgr = self.env.formula_manager
            serialize = self.env.serializer.serialize
            with Solver(env=self.env) as _solver:
                f_type = self.env.stc.get_type(formula)
                eqs = mgr.Iff(formula, res) if f_type.is_bool_type() \
                    else mgr.Equals(formula, res)
                n_eqs = mgr.Not(eqs)
                _solver.add_assertion(n_eqs)
                assert _solver.solve() is False, \
                    f"{serialize(n_eqs)} has model: {_solver.get_model()}"
            assert res in self.env.formula_manager.formulae.values()
            return res

    def walk_toreal(self, formula: FNode, args, **_) -> FNode:
        assert isinstance(formula, FNode)
        assert len(args) == 1
        arg = args[0]
        if arg.is_symbol():
            return self.mgr.ToReal(arg)
        stack = [self.td(arg)]
        new_args = []
        while stack:
            curr = stack.pop()
            while curr.is_toreal():
                curr = curr.arg(0)
            if curr.is_constant():
                val = curr.constant_value()
                assert isinstance(val, int)
                new_args.append(self.mgr.Real(val))
            elif curr.is_plus():
                stack.extend(curr.args())
            elif curr.is_minus():
                stack.append(curr.arg(0))
                rhs = self.mgr.Times(self.mgr.Int(-1), curr.arg(1))
                rhs = self.td(rhs)
                rhs = self.env.simplifier.simplify(rhs)
                stack.append(rhs)
            elif curr.is_times():
                args = list(curr.args())
                symbs = []
                const = 1
                for arg in args:
                    assert not arg.is_plus()
                    assert not arg.is_toreal()
                    assert self.env.stc.get_type(arg).is_int_type()
                    if arg.is_times():
                        args.extend(arg.args())
                    elif arg.is_constant():
                        const *= arg.constant_value()
                        assert isinstance(const, int)
                    else:
                        symbs.append(arg)
                if const == 0:
                    new_args.append(self.mgr.ToReal(0))
                else:
                    args = [self.mgr.ToReal(s) for s in symbs]
                    args.append(self.mgr.Real(const))
                    new_args.append(self.mgr.Times(self._sort(args)))
            else:
                new_args.append(self.mgr.ToReal(curr))
        return self.mgr.Plus(self._sort(new_args))

    def walk_not(self, formula: FNode, args, **_) -> FNode:
        assert isinstance(formula, FNode)
        assert len(args) == 1
        arg = args[0]
        while arg.is_not():
            arg = arg.arg(0)
        if len(arg.args()) == 2:
            args = arg.args()
            if arg.is_lt():
                return self.mgr.GE(args[0], args[1])
            if arg.is_le():
                return self.mgr.GT(args[0], args[1])
        return self.mgr.Not(arg)

    def walk_and(self, formula: FNode, args, **_) -> FNode:
        assert isinstance(formula, FNode)
        return self.mgr.And(
            self._sort(Canonizer._flatten(args, lambda x: x.is_and())))

    def walk_or(self, formula: FNode, args, **_) -> FNode:
        assert isinstance(formula, FNode)
        return self.mgr.Or(
            self._sort(Canonizer._flatten(args, lambda x: x.is_or())))

    def walk_iff(self, formula: FNode, args, **_) -> FNode:
        assert isinstance(formula, FNode)
        return self.mgr.Iff(*self._sort(args))

    def walk_equals(self, formula: FNode, args, **_) -> FNode:
        assert isinstance(formula, FNode)
        assert len(args) == 2
        eq = self.mgr.Equals(*self._sort(args))
        eq = Ineq(self.env, eq, frozenset(), self.td)
        eq = eq.pysmt_ineq()
        if eq.arg(0).is_constant() and eq.arg(1).is_constant():
            if eq.arg(0).constant_value() == eq.arg(1).constant_value():
                return self.mgr.TRUE()
            return self.mgr.FALSE()
        return eq

    def walk_lt(self, formula: FNode, args, **_) -> FNode:
        assert isinstance(formula, FNode)
        assert len(args) == 2
        ineq = self.mgr.LT(args[0], args[1])
        ineq = Ineq(self.env, ineq, frozenset(), self.td)
        ineq = ineq.pysmt_ineq()
        if ineq.arg(0).is_constant() and ineq.arg(1).is_constant():
            if ineq.arg(0).constant_value() < ineq.arg(1).constant_value():
                return self.mgr.TRUE()
            return self.mgr.FALSE()
        return ineq

    def walk_le(self, formula: FNode, args, **_) -> FNode:
        assert isinstance(formula, FNode)
        assert len(args) == 2
        ineq = self.mgr.LE(args[0], args[1])
        ineq = Ineq(self.env, ineq, frozenset(), self.td)
        ineq = ineq.pysmt_ineq()
        if ineq.arg(0).is_constant() and ineq.arg(1).is_constant():
            if ineq.arg(0).constant_value() <= ineq.arg(1).constant_value():
                return self.mgr.TRUE()
            return self.mgr.FALSE()
        return ineq

    def walk_forall(self, formula: FNode, args, **kwargs) -> FNode:
        assert isinstance(formula, FNode)
        qvars = [self.walk_symbol(v, args, **kwargs)
                 for v in formula.quantifier_vars()]
        qvars = self._sort(qvars)
        return self.mgr.ForAll(qvars, args[0])

    def walk_exists(self, formula: FNode, args, **kwargs) -> FNode:
        assert isinstance(formula, FNode)
        qvars = [self.walk_symbol(v, args, **kwargs)
                 for v in formula.quantifier_vars()]
        qvars = self._sort(qvars)
        return self.mgr.Exists(qvars, args[0])

    def walk_plus(self, formula: FNode, args, **_) -> FNode:
        assert isinstance(formula, FNode)
        return self.mgr.Plus(
            self._sort(Canonizer._flatten(args, lambda x: x.is_plus())))

    def walk_times(self, formula: FNode, args, **_) -> FNode:
        assert isinstance(formula, FNode)
        return self.mgr.Times(
            self._sort(Canonizer._flatten(args, lambda x: x.is_times())))

    @staticmethod
    def _flatten(fms: Iterable[FNode], acc) -> Iterator[FNode]:
        args = list(fms)
        while args:
            curr = args.pop()
            if acc(curr):
                args.extend(curr.args())
            else:
                yield curr
