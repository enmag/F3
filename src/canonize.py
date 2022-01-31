from typing import Iterator, Iterable, Optional

from pysmt.environment import Environment as PysmtEnv
from pysmt.walkers import IdentityDagWalker
from pysmt.fnode import FNode

from ineq import Ineq
from rewritings import TimesDistributor
from expr_utils import fnode_key, flatten


class Canonizer(IdentityDagWalker):
    """Rearrange ordering for commutative expressions to increase sharing

    Does not increase depth of the tree representing the formula.
    """

    def __init__(self, env: PysmtEnv):
        assert isinstance(env, PysmtEnv)
        IdentityDagWalker.__init__(self, env=env)
        self.td = TimesDistributor(env=self.env)

    def _sort(self, args: Iterable[FNode]):
        assert isinstance(args, Iterable)
        return sorted(args, key=fnode_key)

    def __call__(self, formula: FNode, **kwargs):
        return self.walk(formula, **kwargs)

    def walk(self, formula: FNode, **kwargs) -> FNode:
        assert formula in self.env.formula_manager.formulae.values()
        res = super().walk(formula, **kwargs)
        assert res in self.env.formula_manager.formulae.values()
        assert formula in self.memoization
        assert res == self.memoization[formula]
        assert res not in self.memoization or res == self.memoization[res]
        assert res == super().walk(res, **kwargs)
        if __debug__:
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
        self.memoization[res] = res
        return res

    def walk_toreal(self, _: FNode, args, **__) -> FNode:
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

    def walk_not(self, _: FNode, args, **__) -> FNode:
        assert len(args) == 1
        arg = args[0]
        c = False
        while arg.is_not():
            arg = arg.arg(0)
            c = not c
        if c:
            return arg
        if len(arg.args()) == 2:
            lhs, rhs = arg.args()
            if arg.is_lt():
                return self.walk_le(None, (rhs, lhs))
            if arg.is_le():
                return self.walk_lt(None, (rhs, lhs))
        return self.mgr.Not(arg)

    def walk_and(self, _: FNode, args, **__) -> FNode:
        return self.mgr.And(
            self._sort(flatten(args, lambda x: x.is_and())))

    def walk_or(self, _: FNode, args, **__) -> FNode:
        return self.mgr.Or(
            self._sort(flatten(args, lambda x: x.is_or())))

    def walk_iff(self, _: FNode, args, **__) -> FNode:
        return self.mgr.Iff(*self._sort(args))

    def walk_equals(self, _: FNode, args, **__) -> FNode:
        assert len(args) == 2
        eq = Ineq(self.env, self.mgr.Equals(*self._sort(args)), frozenset(),
                  self.td).pysmt_ineq()
        if eq.arg(0).is_constant() and eq.arg(1).is_constant():
            if eq.arg(0).constant_value() == eq.arg(1).constant_value():
                return self.mgr.TRUE()
            return self.mgr.FALSE()
        return eq

    def walk_lt(self, _: FNode, args, **__) -> FNode:
        assert len(args) == 2
        ineq = Ineq(self.env, self.mgr.LT(args[0], args[1]), frozenset(),
                    self.td).pysmt_ineq()
        if ineq.arg(0).is_constant() and ineq.arg(1).is_constant():
            if ineq.arg(0).constant_value() < ineq.arg(1).constant_value():
                return self.mgr.TRUE()
            return self.mgr.FALSE()
        return ineq

    def walk_le(self, _: FNode, args, **__) -> FNode:
        assert len(args) == 2
        ineq = Ineq(self.env, self.mgr.LE(args[0], args[1]), frozenset(),
                    self.td).pysmt_ineq()
        if ineq.arg(0).is_constant() and ineq.arg(1).is_constant():
            if ineq.arg(0).constant_value() <= ineq.arg(1).constant_value():
                return self.mgr.TRUE()
            return self.mgr.FALSE()
        return ineq

    def walk_forall(self, _: FNode, __, **___) -> FNode:
        raise Exception("Not implemented")

    def walk_exists(self, _: FNode, __, **___) -> FNode:
        raise Exception("Not implemented")

    def walk_plus(self, _: FNode, args, **__) -> FNode:
        return self.mgr.Plus(
            self._sort(flatten(args, lambda x: x.is_plus())))

    def walk_times(self, _: FNode, args, **__) -> FNode:
        return self.mgr.Times(
            self._sort(flatten(args, lambda x: x.is_times())))
