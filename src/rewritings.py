from typing import Optional

from pysmt.environment import Environment as PysmtEnv
from pysmt.walkers import IdentityDagWalker
from pysmt.rewritings import TimesDistributor as PysmtTimesDistributor
from pysmt.fnode import FNode


class TimesDistributor(PysmtTimesDistributor):
    """Extend pysmt default one with better handling of DIV"""

    def __init__(self, env: PysmtEnv = None,
                 inv_mem: Optional[bool] = None):
        assert isinstance(env, PysmtEnv)
        assert inv_mem is None or isinstance(inv_mem, bool)
        PysmtTimesDistributor.__init__(self, env=env,
                                       invalidate_memoization=inv_mem)
        self.Div = self.env.formula_manager.Div
        self.Real = self.env.formula_manager.Real
        assert self.Times == self.env.formula_manager.Times

    if __debug__:
        def walk(self, formula, **kwargs) -> FNode:
            res = super().walk(formula, **kwargs)
            import pysmt.typing as types
            from solver import Solver
            mgr = self.env.formula_manager
            with Solver(env=self.env) as _solver:
                f_type = self.env.stc.get_type(formula)
                eqs = mgr.Iff(formula, res) if f_type is types.BOOL \
                    else mgr.Equals(formula, res)
                n_eqs = mgr.Not(eqs)
                _solver.add_assertion(n_eqs)
                assert _solver.solve() is False
            return res

    def __call__(self, formula: FNode, **kwargs) -> FNode:
        assert isinstance(formula, FNode)
        assert formula in self.env.formula_manager.formulae.values()
        return self.walk(formula, **kwargs)

    def walk_div(self, _, args, **__) -> FNode:
        """
        From k0(a + b) / (k1(c+d)) to (k0/k1 * a/(c+d)) + (k0/k1 * b/(c+d)),
        where k0, k1 are constants.
        """
        if self.env.stc.get_type(args[0]).is_int_type():
            # integer division.
            return self.Div(args[0], args[1])

        simpl = self.env.simplifier.simplify
        get_free_vars = self.env.fvo.walk
        den = args[1]
        div_const = None
        if den.is_times():
            new_dens = []
            for arg in den.args():
                if len(get_free_vars(arg)) == 0:
                    div_const = self.Times(div_const, arg) if div_const \
                                else arg
                else:
                    new_dens.append(arg)
            den = self.Times(new_dens) if new_dens else None

        if div_const:
            div_const = simpl(self.Div(self.Real(1), div_const))

        stack = [args[0]]
        new_args = []
        while stack:
            const = None
            num = stack.pop()
            if num.is_plus():
                stack.extend(num.args())
            else:
                const = div_const
                if num.is_times():
                    new_nums = []
                    for arg in num.args():
                        if len(get_free_vars(arg)) == 0:
                            const = self.Times(const, arg) if const else arg
                        else:
                            new_nums.append(arg)
                    num = self.Times(new_nums)
                new = self.Div(num, den) if den is not None else num
                if const:
                    new = self.Times(simpl(const), new)
                new_args.append(new)
        return self.Plus(new_args)
