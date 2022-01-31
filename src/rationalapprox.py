from typing import FrozenSet, Set, Dict, Optional, Union
from fractions import Fraction
from collections import defaultdict

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
from pysmt.exceptions import SolverReturnedUnknownResultError
import pysmt.typing as types

from utils import log

_TOLERANCE = 10**-3
_VAL_BOUND = 10000
_APPROX_PRECISION = 3


def set_approx_precision(val: int) -> None:
    global _APPROX_PRECISION
    _APPROX_PRECISION = val


def get_approx_precision() -> int:
    global _APPROX_PRECISION
    return _APPROX_PRECISION


def get_tolerance() -> float:
    global _TOLERANCE
    return _TOLERANCE


def set_tolerance(val: float) -> None:
    global _TOLERANCE
    _TOLERANCE = val


def set_val_bound(val: int) -> None:
    assert isinstance(val, int)
    global _VAL_BOUND
    _VAL_BOUND = val


def get_val_bound() -> int:
    global _VAL_BOUND
    return _VAL_BOUND


class RationalApprox:
    """Approximate value using continued fraction"""

    def __init__(self, maxlen=None):
        """maxlen sets the precision of the approximation"""
        self.cache = defaultdict(list)
        if maxlen is None:
            maxlen = get_approx_precision()
        self.maxlen = maxlen

    def __call__(self, x, maxlen=None):
        return self.approx(x, maxlen)

    def approx(self, val, maxlen=None):
        """approximate value, result is cached"""
        if maxlen is None:
            maxlen = self.maxlen
        assert maxlen <= self.maxlen
        sign = 1
        if val < 0:
            sign = -1
            val = -val
        res = self.cache[val]
        if not res:
            res.extend(continued_fraction(val, self.maxlen))
        assert len(res) <= self.maxlen
        return sign * eval_continued_frac(res[:maxlen], bound=get_val_bound())

    def simpl_model(self, env: PysmtEnv, solver,
                    params: Union[Set[FNode], FrozenSet[FNode]],
                    whole: Optional[FNode] = None) -> Dict[FNode, FNode]:
        assert isinstance(env, PysmtEnv)
        assert isinstance(params, (set, frozenset))
        assert all(isinstance(p, FNode) for p in params)
        assert whole is None or whole in params
        assert all(p in env.formula_manager.get_all_symbols() for p in params)
        assert all(p.symbol_type().is_int_type() or
                   p.symbol_type().is_real_type()
                   for p in params)
        mgr = env.formula_manager
        model = solver.get_values(params)

        if whole is not None and model[whole].is_constant(_type=types.REAL):
            d_val = model[whole]
            # remove denominator from d_val
            assert hasattr(d_val.constant_value(), "numerator")
            assert hasattr(d_val.constant_value(), "denominator")
            assert d_val.constant_value().denominator > 0
            simpl = env.simplifier.simplify
            den = mgr.Real(d_val.constant_value().denominator)
            model = {p: simpl(mgr.Times(model[p], den))
                     for p in params}
            assert model[whole].constant_value() == d_val.constant_value().numerator

        for k, v in model.items():
            val = self(v.constant_value())
            val = mgr.Real(val) if v.is_real_constant() \
                else mgr.Int(int(val))
            eq = mgr.Equals(k, val)
            solver.add_assertion(eq)
        try:
            if solver.solve() is True:
                return solver.get_values(params)
        except SolverReturnedUnknownResultError:
            pass
        log("\tModel simplification failed")
        return model


# def approx_num(val, maxlen):
#     """Approximate val using maxlen terms of continued fractions"""
#     n, d, num, den = 0, 1, 1, 0
#     for u in continued_fraction(val, maxlen):
#         n, d, num, den = num, den, num * u + n, den * u + d
#     return Fraction(num, den)


def eval_continued_frac(seq, bound=-1):
    n, d, num, den = 0, 1, 1, 0
    for u in seq:
        new_den = den * u + d
        if 0 < bound <= new_den:
            break
        n, d, num, den = num, den, num * u + n, new_den
    assert den <= get_val_bound()
    return Fraction(num, den)


def continued_fraction(x, maxlen):
    """generate sequece of terms of continued fraction"""
    if isinstance(x, Fraction):
        return _int_cont_frac(x.numerator, x.denominator, maxlen)
    if isinstance(x, (tuple, list)):
        assert len(x) == 2
        return _int_cont_frac(x[0], x[1], maxlen)
    if isinstance(x, float):
        return _float_cont_frac(x, maxlen)
    if isinstance(x, int):
        return [max(min(x, get_val_bound()), -get_val_bound())]
    raise TypeError('Unsupported input type {:}'.format(type(x)))


def _int_cont_frac(num, den, max_amount):
    abs_tol = get_tolerance()
    fractional_part = abs_tol + 1  # something greater than abs_tol
    real_number = Fraction(num, den)
    amount = 0
    while abs(fractional_part) > abs_tol and amount < max_amount and den != 0:
        integer_part = num // den
        fractional_part = real_number - integer_part
        assert isinstance(fractional_part, Fraction)
        if fractional_part != 0:
            real_number = Fraction(fractional_part.denominator,
                                   fractional_part.numerator)
        num -= integer_part * den
        num, den = den, num
        amount += 1
        yield integer_part

    # while den != 0 and amount < max_amount:
    #     integer_part = num // den
    #     num -= integer_part * den
    #     num, den = den, num
    #     amount += 1
    #     yield integer_part


def _float_cont_frac(real_number, max_amount):
    abs_tol = get_tolerance()
    fractional_part = abs_tol + 1  # something greater than abs_tol
    amount = 0
    while abs(fractional_part) > abs_tol and amount < max_amount:
        integer_part = int(round(real_number, 10))
        fractional_part = real_number - integer_part
        if fractional_part != 0:
            real_number = 1.0 / fractional_part
        amount += 1
        yield integer_part
