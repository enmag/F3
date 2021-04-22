from typing import Tuple, Optional
from collections import defaultdict, Iterable
from fractions import Fraction

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
import pysmt.typing as types
from pysmt.typing import PySMTType

from rewritings import TimesDistributor
from utils import default_key, symb_is_next
from expr_at_time import ExprAtTime

# TODO: here we parse a FNode in multiple places
# TODO: refactor in a single function.


class Ineq:
    """Equality or Inequality with operator < or <=

    All equalities / inequalities are represented as:
    k op alpha
    where:
          op is =, <, <=
          k is a constant
          alpha is an expression
    """
    LT = -1
    LE = 1
    EQ = 0

    def __init__(self, env: PysmtEnv, ineq: FNode, params: Iterable,
                 td: TimesDistributor):
        """ineq should have all multiplications pushed at the leaves"""
        assert isinstance(env, PysmtEnv)
        assert isinstance(ineq, FNode)
        assert isinstance(params, Iterable)
        assert isinstance(td, TimesDistributor)
        assert ineq.is_equals() or ineq.is_le() or ineq.is_lt(), \
            "Not =, < or <= : {}".format(ineq.serialize())
        self.env = env
        self.params = frozenset(params)
        self._type = Ineq.EQ
        if ineq.is_le():
            self._type = Ineq.LE
        elif ineq.is_lt():
            self._type = Ineq.LT
        self._lhs, self._rhs = Ineq._parse(env, ineq, self.params, td)

        if __debug__:
            from solver import Solver
            mgr = self.env.formula_manager
            with Solver(env=env) as solver:
                eq = mgr.Iff(ineq, self.pysmt_ineq())
                n_eq = mgr.Not(eq)
                solver.add_assertion(n_eq)
                if solver.solve():
                    assert False, "{} : {}".format(eq.serialize(),
                                                   solver.get_model())

    def is_eq(self) -> bool:
        "True iff current ineq is an equality"
        return self._type == Ineq.EQ

    def is_lt(self) -> bool:
        "True iff current ineq is a less than"
        return self._type == Ineq.LT

    def is_le(self) -> bool:
        "True iff current ineq is a less or equal"
        return self._type == Ineq.LE

    @property
    def rhs(self):
        "rhs is an Expr representing a constant value."
        return self._rhs

    @property
    def lhs(self) -> dict:
        """Dictionary: FNode -> Expr

        The keys of type FNode are a product of symbols.
        The values of type Expr represent a constant coefficient.
        """
        return self._lhs

    def to_real(self):
        mgr = self.env.formula_manager
        if self.rhs.expr_type is not types.REAL:
            if self.is_lt():
                self._rhs.plus_const(-1)
                self._type = Ineq.LE
            self._rhs = self._rhs.get_real()
            new_lhs = defaultdict(lambda: Expr(self.env, types.REAL,
                                               self.rhs.td))
            for k, v in self._lhs.items():
                assert self.env.stc.get_type(k) is types.INT
                assert v.expr_type is types.INT
                new_lhs[mgr.ToReal(k)] = v.get_real()
            self._lhs = new_lhs
        assert self.rhs.expr_type is types.REAL
        assert all(self.env.stc.get_type(k) is types.REAL
                   for k in self._lhs.keys())
        assert all(v.expr_type is types.REAL
                   for v in self._lhs.values())

    def pysmt_ineq(self) -> FNode:
        "Convert Ineq into FNode"
        mgr = self.env.formula_manager
        expr = sorted([k if v.is_one()
                       else mgr.Times(k, v.pysmt_expr())
                       for k, v in self.lhs.items() if not v.is_zero()],
                      key=default_key)
        expr = mgr.Plus(expr) if expr else self.rhs.number(0)
        rhs = self.rhs.pysmt_expr()
        if self.is_eq():
            expr = mgr.Equals(expr, rhs)
        elif self.is_le():
            expr = mgr.LE(expr, rhs)
        else:
            assert self.is_lt()
            expr = mgr.LT(expr, rhs)
        return expr

    @staticmethod
    def _parse(env: PysmtEnv, ineq: FNode, params: Iterable,
               td: TimesDistributor) -> Tuple[dict, FNode]:
        assert isinstance(env, PysmtEnv)
        assert isinstance(ineq, FNode)
        assert isinstance(params, Iterable)
        assert isinstance(td, TimesDistributor)

        ineq_type = env.stc.get_type(ineq.arg(0))
        assert ineq_type.is_real_type() or ineq_type.is_int_type()

        mgr = env.formula_manager
        pysmt_num = None
        if ineq_type.is_int_type():
            pysmt_num = mgr.Int
        else:
            pysmt_num = mgr.Real

        m_one = pysmt_num(-1)
        m_one_expr = Expr(env, ineq_type, td, const=-1)

        lhs = defaultdict(lambda: Expr(env, ineq_type, td))
        rhs = Expr(env, ineq_type, td)
        stack = [td(ineq.arg(0)), td(mgr.Times(m_one, ineq.arg(1)))]
        while stack:
            curr = stack.pop()
            # if all symbols are parameters this is a "constant".
            if env.fvo.get_free_variables(curr) <= params:
                rhs.plus_fnode(curr)
            elif curr.is_symbol():
                lhs[curr].plus_const(1)
            elif curr.is_plus():
                stack.extend(curr.args())
            elif curr.is_minus():
                stack.append(curr.arg(0))
                stack.append(td(mgr.Times(m_one, curr.arg(1))))
            elif curr.is_times():
                args = list(curr.args())
                const = 1
                symbs = []
                _params = []
                for arg in args:
                    assert not arg.is_plus(), curr.serialize()
                    if arg.is_times():
                        args.extend(arg.args())
                    elif arg.is_constant():
                        const *= arg.constant_value()
                    elif arg.is_symbol():
                        if arg in params:
                            _params.append(arg)
                        else:
                            symbs.append(arg)
                    elif arg.is_div():
                        # TODO: we could rewrite integer division as mult
                        symbs.append(arg)
                    elif arg.is_toreal():
                        # ToReal(s) and s are considered as 2 different symbols.
                        assert arg.arg(0).is_symbol(), curr.serialize()
                        if arg.arg(0) in params:
                            _params.append(arg)
                        else:
                            symbs.append(arg)
                    else:
                        assert False, "Unhandled op: {}".format(arg)
                        # symbs.append(arg)
                symbs.sort(key=default_key)
                symbs = mgr.Times(symbs)
                coeff = mgr.Times(pysmt_num(const), *_params)
                lhs[symbs].plus_fnode(coeff)
            elif curr.is_div():
                # here we just leave it as it is
                lhs[curr].plus_const(1)
            elif curr.is_toreal():
                # ToReal(s) and s are considered as 2 different symbols.
                assert curr.arg(0).is_symbol(), curr
                if curr.arg(0) in params:
                    rhs.plus_fnode(curr)
                else:
                    lhs[curr].plus_const(1)
            else:
                assert False, curr

        rhs.times(m_one_expr)
        return lhs, rhs

    def __repr__(self) -> str:
        if self.lhs:
            res = " + ".join("{} * {}".format(repr(val), repr(key))
                             for key, val in self.lhs.items())
        else:
            res = "0"

        if self.is_lt():
            res += " < "
        elif self.is_le():
            res += " <= "
        else:
            res += " = "

        res += repr(self.rhs)
        return res

    # EOC Ineq


class Expr:
    "Represent a sum of products, apply simplifications"

    def __init__(self, env: PysmtEnv, expr_type: PySMTType,
                 td: TimesDistributor, formula: Optional[FNode] = None,
                 expr=None, const=None):
        assert isinstance(env, PysmtEnv)
        assert isinstance(expr_type, PySMTType)
        assert isinstance(td, TimesDistributor)
        assert formula is None or isinstance(formula, FNode)
        assert expr is None or isinstance(expr, Expr)
        assert const is None or isinstance(const, (float, int, Fraction)), \
            (const, type(const))
        assert expr_type.is_real_type() or expr_type.is_int_type()

        self.env = env
        self.mgr = env.formula_manager
        self.expr_type = expr_type
        self.td = td

        # symbs to coefficient.
        self.symb2coef = defaultdict(int)
        if self.expr_type.is_real_type():
            self.number = self.mgr.Real
        else:
            self.number = self.mgr.Int

        if formula:
            self.plus_fnode(formula)
        if const:
            self.plus_const(const)
        if expr:
            self.plus(expr)

        if __debug__:
            if expr_type.is_real_type():
                const = self.mgr.Real(const) if const else const
                formula = self.mgr.ToReal(formula) if formula and \
                    self.env.stc.get_type(formula).is_int_type() \
                    else formula
                if expr is not None and expr.expr_type.is_int_type():
                    expr = expr.get_real()
            else:
                assert expr_type.is_int_type()
                assert formula is None or \
                    self.env.stc.get_type(formula).is_int_type(), formula
                const = self.mgr.Int(const) if const else const

            assert expr is None or expr.expr_type == self.expr_type, expr
            assert formula is None or \
                self.env.stc.get_type(formula) == self.expr_type
            in_f = [f for f in [formula, expr, const] if f is not None]
            if in_f:
                from solver import Solver
                with Solver(env=self.env) as solver:
                    expr = self.mgr.Plus(in_f)
                    eq = self.mgr.Equals(expr, self.pysmt_expr())
                    n_eq = self.mgr.Not(eq)
                    solver.add_assertion(n_eq)
                    if solver.solve():
                        assert False, "{} : {}".format(eq, solver.get_model())

    def is_zero(self) -> bool:
        """Return true if self is zero"""
        if len(self.symb2coef) == 0:
            return True

        return all(v == 0 for v in self.symb2coef.values())

    def is_one(self) -> bool:
        """Return true if self is one"""
        if len(self.symb2coef) == 0:
            return False
        one = self.number(1)
        if len(self.symb2coef) == 1 and \
           one in self.symb2coef and \
           self.symb2coef[one] == 1:
            return True
        return False

    def clone(self):
        "Return new instance of Expr representing the same expression"
        res = Expr(self.env, self.expr_type, self.td)
        res.symb2coef = {k: v for k, v in self.symb2coef.items() if v != 0}
        return res

    def get_real(self):
        "self must be of integer type, return expression where leaves are real"
        assert self.expr_type.is_int_type(), self
        one = self.number(1)
        res = Expr(self.env, types.REAL, self.td)
        res.symb2coef = {self.mgr.ToReal(k) if k is not one else
                         self.mgr.Real(1): v
                         for k, v in self.symb2coef.items() if v != 0}
        return res

    def plus_const(self, num) -> None:
        "Sum constant number to expression"
        assert self.expr_type.is_real_type() or isinstance(num, int)
        self.symb2coef[self.number(1)] += num

    def plus_fnode(self, formula: FNode) -> None:
        """Sum pysmt expression to current expression.

        """
        assert isinstance(formula, FNode)
        # assert self.env.stc.get_type(formula) == self.expr_type
        assert self.expr_type.is_real_type() or \
            self.expr_type == self.env.stc.get_type(formula)
        do_to_real = self.expr_type.is_real_type() and \
            self.env.stc.get_type(formula).is_int_type()
        one = self.number(1)
        m_one = self.number(-1)
        stack = [self.td(formula)]
        while stack:
            curr = stack.pop()
            if curr.is_constant() or \
               len(self.get_free_variables(curr)) == 0:
                val = self.simplify(curr).constant_value()
                self.symb2coef[one] += val
                if self.symb2coef[one] == 0:
                    self.symb2coef.pop(one, None)
            elif curr.is_symbol() or curr.is_toreal():
                assert (not curr.is_toreal()) or curr.arg(0).is_symbol()
                if do_to_real and curr.symbol_type().is_int_type():
                    curr = self.mgr.ToReal(curr)
                self.symb2coef[curr] += 1
            elif curr.is_plus():
                stack.extend(curr.args())
            elif curr.is_minus():
                stack.append(curr.arg(0))
                rhs = self.mgr.Times(m_one, curr.arg(1))
                stack.append(self.td(rhs))
            elif curr.is_times():
                factors = list(curr.args())
                const = 1
                symbs = []
                for factor in factors:
                    assert not factor.is_plus(), "{}".format(factor)
                    assert not factor.is_minus(), "{}".format(factor)
                    if factor.is_times():
                        factors.extend(factor.args())
                    elif factor.is_symbol() or factor.is_toreal():
                        assert (not factor.is_toreal()) or \
                            factor.arg(0).is_symbol()
                        symbs.append(factor)
                    elif factor.is_constant() or \
                            len(self.get_free_variables(factor)) == 0:
                        const *= self.simplify(factor).constant_value()
                    elif factor.is_div():
                        symbs.append(factor)
                    elif factor.is_toreal():
                        assert factor.arg(0).is_symbol()
                        symbs.append(factor)
                    else:
                        symbs.append(factor)
                        print("Expr - Unhandled op: {}".format(factor))
                symbs = self.mgr.Times(sorted(symbs,
                                              key=default_key)) \
                    if symbs else one
                if symbs is not one and do_to_real:
                    symbs = self.mgr.ToReal(symbs)
                self.symb2coef[symbs] += const
                if self.symb2coef[symbs] == 0:
                    self.symb2coef.pop(symbs, None)
            elif curr.is_div():
                if do_to_real:
                    curr = self.mgr.ToReal(curr)
                self.symb2coef[curr] += 1
            else:
                assert False, curr

    def times_fnode(self, formula: FNode) -> None:
        """Multiply pysmt expression to current expression.

        Expressions types must match.
        """
        assert isinstance(formula, FNode)
        assert self.env.stc.get_type(formula) == self.expr_type
        if not formula.is_one():
            expr = Expr(self.env, self.expr_type, self.td, formula=formula)
            self.times(expr)

    def plus(self, *exprs):
        "Sum given exprs to self"
        for expr in exprs:
            assert expr.expr_type == self.expr_type
            for k, v in expr.symb2coef.items():
                self.symb2coef[k] += v
        return self

    def times(self, *exprs):
        "Multiply self for the given exprs"
        if self.is_zero():
            return self
        for expr in exprs:
            assert isinstance(expr, Expr)
            assert self.expr_type.is_real_type() or \
                expr.expr_type == self.expr_type, \
                "{} -- {}".format(expr, self)
            if expr.is_zero():
                self.symb2coef.clear()
                return self
            if not expr.is_one():
                if expr.expr_type.is_int_type() and \
                   self.expr_type.is_real_type():
                    expr = expr.get_real()
                symb2coef0 = self.symb2coef
                symb2coef1 = expr.symb2coef
                self.symb2coef = defaultdict(int)
                for k0, v0 in symb2coef0.items():
                    for k1, v1 in symb2coef1.items():
                        symbs = list(k0.args()) if k0.is_times() else [k0]
                        if k1.is_times():
                            symbs.extend(k1.args())
                        else:
                            if not k1.is_one():
                                symbs.append(k1)
                        symbs.sort(key=default_key)
                        symbs = self.mgr.Times(symbs)
                        self.symb2coef[symbs] += v0 * v1
        return self

    def simplify(self, formula: FNode) -> FNode:
        assert isinstance(formula, FNode)
        return self.env.simplifier.simplify(formula)

    def get_free_variables(self, formula: FNode):
        assert isinstance(formula, FNode)
        return self.env.fvo.get_free_variables(formula)

    def pysmt_expr(self) -> FNode:
        "Convert Expr into FNode"
        keys = sorted(self.symb2coef.keys(), key=default_key)
        to_add = [self._fnode_times(k, self.symb2coef[k])
                  for k in keys if self.symb2coef[k] != 0]
        if to_add:
            return self.mgr.Plus(to_add)
        return self.number(0)

    def _fnode_times(self, lhs: FNode, rhs) -> FNode:
        assert isinstance(lhs, FNode)
        assert not isinstance(rhs, FNode)
        if rhs == 0:
            return self.number(0)
        if rhs == 1:
            return lhs
        if lhs == self.number(0):
            return lhs
        if lhs == self.number(1):
            return self.number(rhs)
        if lhs.is_symbol() or lhs.is_toreal():
            assert lhs.is_symbol() or lhs.arg(0).is_symbol()
            return self.mgr.Times(lhs, self.number(rhs))
        if lhs.is_times():
            return self.mgr.Times(*lhs.args(), self.number(rhs))
        assert lhs.is_div(), (lhs, rhs)
        return self.mgr.Times(lhs, self.number(rhs))

    def __str__(self) -> str:
        return str(self.pysmt_expr())

    def __repr__(self) -> str:
        return self.pysmt_expr().serialize()

    # EOC Expr


def eq_to_assign(env: PysmtEnv, equality: FNode,
                 td: TimesDistributor,
                 _time: Optional[int] = None) -> Tuple[FNode, Optional[FNode],
                                                       Optional[bool]]:
    """Return k, v where k is a symbol and v is an expression.
    Return None, None if the rewriting failed.

    Return TRUE, None if equality is trivial.
    In case of success k = v is equivalent to the input equality.
    """
    assert isinstance(env, PysmtEnv)
    assert isinstance(equality, FNode)
    assert isinstance(td, TimesDistributor)
    assert equality in env.formula_manager.formulae.values()
    if equality.is_true():
        return equality, None, None
    assert equality.is_equals()
    assert _time is None or isinstance(_time, int)
    assert _time is None or _time >= 0

    mgr = env.formula_manager
    expr_type = env.stc.get_type(equality.arg(0))
    expr = Expr(env, expr_type, td,
                mgr.Minus(equality.arg(0), equality.arg(1)))

    if expr.is_zero():  # 0 = 0
        if __debug__:
            from solver import Solver
            with Solver(env=env) as solver:
                solver.add_assertion(mgr.Not(equality))
                assert solver.solve() is False
        return mgr.TRUE(), None, None

    _symb = None
    _coef = None
    _is_next = False
    for k in sorted(expr.symb2coef.keys(), key=default_key):
        v = expr.symb2coef[k]
        if k.is_symbol() and v != 0:
            is_next = ExprAtTime.get_symb_time(mgr, k)[1] == _time if _time \
                      else symb_is_next(k)
            if not _is_next or is_next:
                assert not isinstance(v, FNode)
                if v in {-1, 1} or (not _is_next and is_next):
                    _symb, _coef, _is_next = k, v, is_next
                # try to get the most "nice" looking assignment.
                if expr_type.is_real_type():
                    if _coef is None or \
                       (v < 0 < _coef) or \
                       (_coef < 0 and v > _coef) or \
                       (_coef > 0 and v < _coef):
                        _symb, _coef, _is_next = k, v, is_next
                if _coef == -1 and is_next:
                    break

    if _symb is None:
        return None, None, None
    assert _symb is not None
    assert _coef is not None

    if _coef in {-1, 1}:
        coef_expr = -_coef
    else:
        frac_coef = Fraction(-1, _coef)
        int_coef = round(Fraction(-1, _coef))
        coef_expr = int_coef if int_coef == frac_coef else frac_coef
    if expr_type.is_int_type() and not isinstance(coef_expr, int):
        return None, None, None  # TODO: ToReal
    coef_expr = Expr(env, expr_type, td,
                     const=coef_expr)
    # remove term with _symb
    expr.symb2coef.pop(_symb)
    # multiply by inverse of the opposite coefficient
    expr.times(coef_expr)

    assert _symb not in expr.pysmt_expr().get_free_variables()
    if __debug__:
        from solver import Solver
        with Solver(env=env) as solver:
            _rv = mgr.Equals(_symb, expr.pysmt_expr())
            _iff = mgr.Iff(equality, _rv)
            solver.add_assertion(mgr.Not(_iff))
            assert solver.solve() is False
    return _symb, expr.pysmt_expr(), _is_next
