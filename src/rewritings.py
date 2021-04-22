from collections.abc import Iterable

from pysmt.environment import Environment as PysmtEnv
from pysmt.walkers import IdentityDagWalker, handles
from pysmt.rewritings import TimesDistributor as PysmtTimesDistributor
from pysmt.rewritings import NNFizer
from pysmt.fnode import FNode
import pysmt.operators as op

from solver import UnsatCoreSolver, Solver


# class DNFizer(IdentityDagWalker):
#     """Rewrite formula in disjunctive normal form"""

#     def __init__(self, env: PysmtEnv = None):
#         assert env is None or isinstance(env, PysmtEnv)
#         IdentityDagWalker.__init__(self, env)

#         self.mgr = self.env.formula_manager
#         self._nnf = NNFizer(environment=self.env)
#         self._dnf_pieces = {}

#     def simplify(self, formula: FNode):
#         assert isinstance(formula, FNode)
#         assert formula in self.mgr.formulae.values()
#         return self.env.simplifier.simplify(formula)

#     def generate(self, formula: FNode) -> Iterable:
#         """Returns iterable of conjunctive formulae.

#         Each conjunct implies the input formula
#         """
#         assert isinstance(formula, FNode)
#         formula = self.simplify(formula)
#         n_f = self.simplify(self.mgr.Not(formula))
#         tmp_env = PysmtEnv()
#         tmp_mgr = tmp_env.formula_manager
#         tmp_n_f = tmp_mgr.normalize(n_f)
#         with Solver(env=self.env) as solver, \
#             UnsatCoreSolver(env=tmp_env,
#                             unsat_cores_mode="named") as tmp_solver:
#             # assert formula in solver
#             solver.add_assertion(formula)

#             # push not(formula) in tmp
#             tmp_solver.add_assertion(tmp_n_f, named="nf")

#             while solver.solve():
#                 tmp_solver.push()
#                 # get atom assignments in solver
#                 atoms = [a if solver.get_py_value(a) else self.mgr.Not(a)
#                          for a in formula.get_atoms()]
#                 for i, a in enumerate(atoms):
#                     if a.is_not() and a.arg(0).is_equals():
#                         a = a.arg(0)
#                         _gt = self.mgr.GT(a.arg(0), a.arg(1))
#                         a = _gt if solver.get_py_value(_gt) \
#                             else self.mgr.LT(a.arg(0), a.arg(1))

#                     a = tmp_mgr.normalize(a)
#                     tmp_solver.add_assertion(a, named="a{}".format(i))
#                 res = tmp_solver.solve()
#                 assert res is False
#                 core = tmp_solver.get_named_unsat_core()
#                 core = self.mgr.And([self.mgr.normalize(c)
#                                      for k, c in core.items() if k != "nf"])
#                 tmp_solver.pop()

#                 solver.add_assertion(self.mgr.Not(core))
#                 yield core

#     def convert(self, formula: FNode) -> FNode:
#         """Convert formula into an Equisatisfiable DNF.
#         Returns an FNode.
#         """
#         assert isinstance(formula, FNode)
#         formula = self._nnf.convert(formula)
#         dnf = self.walk(formula)
#         return dnf

#     def serialize(self, _dnf):
#         cubes = []
#         for cube in _dnf:
#             cubes.append("{ " + ", ".join(str(lit) for lit in cube) + " }")
#         res = "[" + "; ".join(cubes) + "]"
#         return res

#     @handles(op.QUANTIFIERS)
#     def walk_quantifier(self, formula, args, **kwargs):
#         raise NotImplementedError("DNFizer does not support quantifiers")

#     def walk_and(self, formula, args, **kwargs):
#         """DNF for conjunction

#         (a | b) & (c | d)
#         DNF: (a & c) | (a & d) | (b & c) | (b & d)
#         """
#         if len(args) == 1:
#             return args[0]

#         stack = args
#         conjunctions = []
#         while stack:
#             curr = stack.pop()
#             if curr.is_and():
#                 stack.extend(curr.args())
#             else:
#                 assert curr.is_or() or curr.is_not() or \
#                     curr.is_constant() or curr.is_symbol() or \
#                     curr.is_theory_relation(), curr
#                 conjunctions.append(curr)
#         res = self.mgr.FALSE()
#         for i0 in range(len(conjunctions)):
#             c0s = conjunctions[i0]
#             c0s = c0s.args() if c0s.is_or() else [c0s]
#             for i1 in range(i0+1, len(conjunctions)):
#                 c1s = conjunctions[i1]
#                 c1s = c1s.args() if c1s.is_or() else [c1s]
#                 for c0 in c0s:
#                     for c1 in c1s:
#                         conj = self.simplify(self.mgr.And(c0, c1))
#                         res = self.simplify(self.mgr.Or(res, conj))
#                         if res.is_true():
#                             self._dnf_pieces[formula] = res
#                             return res
#         self._dnf_pieces[formula] = res
#         return res

#     def walk_or(self, _, args, **kwargs):
#         """DNF for disjunction"""
#         return self.simplify(self.mgr.Or(args))

#     def walk_not(self, _, args, **kwargs):
#         """DNF for negation"""
#         assert len(args) == 1
#         arg = args[0]
#         assert arg.is_constant() or arg.is_symbol()
#         return self.mgr.Not(arg)

#     def walk_implies(self, formula,  args, **kwargs):
#         raise NotImplementedError("DNFizer does not support implication")

#     def walk_iff(self, formula, args, **kwargs):
#         raise NotImplementedError("DNFizer does not support iff")

# # EOC DNFizer


class TimesDistributor(PysmtTimesDistributor):
    """Extend pysmt default one with better handling of DIV"""

    def __init__(self, env: PysmtEnv = None, inv_mem=None):
        assert isinstance(env, PysmtEnv)
        PysmtTimesDistributor.__init__(self, env=env,
                                       invalidate_memoization=inv_mem)
        self.Div = self.env.formula_manager.Div
        self.Real = self.env.formula_manager.Real

    if __debug__:
        def walk(self, formula, **kwargs) -> FNode:
            res = super().walk(formula, **kwargs)
            import pysmt.typing as types
            mgr = self.env.formula_manager
            with Solver(env=self.env) as solver:
                f_type = self.env.stc.get_type(formula)
                eqs = mgr.Iff(formula, res) if f_type is types.BOOL \
                    else mgr.Equals(formula, res)
                n_eqs = mgr.Not(eqs)
                solver.add_assertion(n_eqs)
                assert solver.solve() is False, \
                    "{} has model: {}".format(n_eqs.serialize(),
                                              solver.get_model())
            return res

    def __call__(self, formula: FNode, **kwargs) -> FNode:
        return self.walk(formula, **kwargs)

    def walk_div(self, formula: FNode, args, **kwargs) -> FNode:
        """
        From k0(a + b) / (k1(c+d)) to (k0/k1 * a/(c+d)) + (k0/k1 * b/(c+d)),
        where k0, k1 are constants.
        """
        if self.env.stc.get_type(args[0]).is_int_type():
            return self.Div(args[0], args[1])
        simplifier = self.env.simplifier
        den = args[1]
        div_const = None
        if den.is_times():
            new_dens = []
            for arg in den:
                if len(self.env.fvo.get_free_variables(arg)) == 0:
                    div_const = self.Times(div_const, arg) if div_const \
                                else arg
                else:
                    new_dens.append(arg)
            den = self.Times(new_dens)
        elif formula.is_div() and formula.arg(1).is_times():
            new_dens = []
            for arg in formula.arg(1).args():
                if len(self.env.fvo.get_free_variables(arg)) == 0:
                    div_const = self.Times(div_const, arg) if div_const \
                                else arg
                else:
                    new_dens.append(arg)
            den = self.walk(self.Times(new_dens))

        if div_const:
            div_const = simplifier.simplify(self.Div(self.Real(1), div_const))

        stack = [args[0]]
        new_args = []
        while stack:
            const = None
            num = stack.pop()
            if num.is_plus():
                stack.extend(num.args())
            else:
                if num.is_times():
                    const = div_const
                    new_nums = []
                    for arg in num.args():
                        if len(self.env.fvo.get_free_variables(arg)) == 0:
                            const = self.Times(const, arg) if const else arg
                        else:
                            new_nums.append(arg)
                    num = self.Times(new_nums)
                new = self.Div(num, den)
                if const:
                    const = simplifier.simplify(const)
                    new = self.Times(const, new)
                new_args.append(new)
        return self.Plus(new_args)
