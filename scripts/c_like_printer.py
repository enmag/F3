from typing import Optional, Dict
from io import StringIO

from pysmt.environment import Environment as PysmtEnv
from pysmt.printers import HRPrinter, HRSerializer
from pysmt.constants import is_pysmt_fraction
from pysmt.fnode import FNode
from pysmt.walkers.generic import handles
import pysmt.operators as op


class CPrinter(HRPrinter):
    """Performs serialization of a formula in C-like format.
    E.g., Implies(And(Symbol(x), Symbol(y)), Symbol(z))  ~>   '(x && y) -> z'
    """

    def c_type(self, pysmt_t):
        if pysmt_t.is_bool_type():
            self.write("bool")
        elif pysmt_t.is_int_type():
            self.write("int")
        else:
            assert pysmt_t.is_real_type(), str(pysmt_t)
            self.write("float")

    def __init__(self, stream: StringIO, env: PysmtEnv = None):
        assert env is None or isinstance(env, PysmtEnv)
        HRPrinter.__init__(self, stream, env=env)
        assert self.env is not None
        self.stream = stream
        self.write = self.stream.write
        # self._next_op_re = re.compile(r"next(\S+)")

    def walk_symbol(self, formula: FNode) -> None:
        assert isinstance(formula, FNode)
        HRPrinter.walk_symbol(self, formula)
        # is_bool = formula.symbol_type().is_bool_type()
        # if is_bool:
        #     self.write("(")
        # HRPrinter.walk_symbol(self, formula)
        # if is_bool:
        #     self.write(" != 0)")

    def walk_real_constant(self, formula: FNode) -> None:
        assert isinstance(formula, FNode)
        assert is_pysmt_fraction(formula.constant_value()), \
            "The type was " + str(type(formula.constant_value()))
        # TODO: Remove this once issue 113 in gmpy2 is solved
        v = formula.constant_value()
        n, d = v.numerator, v.denominator
        if n < 0 and d < 0:
            n = -n
            d = -d
        sign = ""
        if n < 0 or d < 0:
            sign = "-"
            n = abs(n)
            d = abs(d)
        if n == 0:
            self.write("0.0")
        elif d == 1:
            # need to keep it as real otherwise a division becomes int div.
            self.write("{}{}.0".format(sign, n))
        else:
            self.write("{}({}.0/{}.0)".format(sign, n, d))

    def walk_bool_constant(self, formula: FNode):
        assert isinstance(formula, FNode)
        if formula.constant_value():
            self.write("1")
        else:
            self.write("0")

    def walk_pow(self, formula: FNode):
        assert False
        assert isinstance(formula, FNode)
        assert len(formula.args()) == 2
        assert formula.arg(1).is_int_constant()
        assert formula.arg(1).constant_value() >= 0
        exp = formula.arg(1).constant_value()
        if exp == 0:
            self.write("1")
        else:
            self.write("(")
            for _ in range(exp - 1):
                yield formula.arg(0)
                self.write(" * ")
            yield formula.arg(0)
            self.write(")")

    def walk_array_select(self, formula: FNode):
        assert False, "not supported"
        assert isinstance(formula, FNode)
        yield formula.arg(0)
        self.write("[")
        yield formula.arg(1)
        self.write("]")

    def walk_ite(self, formula: FNode):
        assert isinstance(formula, FNode)
        self.write("(")
        yield formula.arg(0)
        self.write(" ? ")
        yield formula.arg(1)
        self.write(" : ")
        yield formula.arg(2)
        self.write(")")

    def walk_not(self, formula: FNode):
        self.write("( !")
        yield formula.arg(0)
        self.write(")")

    def walk_and(self, formula: FNode):
        self.write("(")
        yield formula.arg(0)
        self.write(" && ")
        yield formula.arg(1)
        self.write(")")

    def walk_or(self, formula: FNode):
        self.write("(")
        yield formula.arg(0)
        self.write(" || ")
        yield formula.arg(1)
        self.write(")")

    def walk_implies(self, formula: FNode):
        self.write("( !")
        yield formula.arg(0)
        self.write(" || ")
        yield formula.arg(1)
        self.write(")")

    def walk_iff(self, formula: FNode):
        self.write("(")
        yield formula.arg(0)
        self.write(" == ")
        yield formula.arg(1)
        self.write(")")

    def walk_equals(self, formula: FNode):
        self.write("(")
        yield formula.arg(0)
        self.write(" == ")
        yield formula.arg(1)
        self.write(")")

    def walk_bv_constant(self, formula: FNode):
        # This is the simplest SMT-LIB way of printing the value of a BV
        # self.write("(_ bv%d %d)" % (formula.bv_width(),
        #                             formula.constant_value()))
        assert False, "not supported bv_constant: " \
            "`{}` `{}`".format(formula.constant_value(), formula.bv_width())
        self.write("0ub{}_{}".format(formula.bv_width(),
                                     formula.constant_value()))

    def walk_bv_ror(self, formula: FNode):
        assert False, "not supported"
        self.write("(")
        yield formula.arg(0)
        self.write(" ROR ")
        self.write("%d)" % formula.bv_rotation_step())

    def walk_bv_rol(self, formula: FNode):
        assert False, "not supported"
        self.write("(")
        yield formula.arg(0)
        self.write(" ROL ")
        self.write("%d)" % formula.bv_rotation_step())

    def walk_bv_zext(self, formula: FNode):
        assert False, "not supported"
        self.write("(")
        yield formula.arg(0)
        self.write(" ZEXT ")
        self.write("%d)" % formula.bv_extend_step())

    def walk_bv_sext(self, formula: FNode):
        assert False, "not supported"
        self.write("(")
        yield formula.arg(0)
        self.write(" SEXT ")
        self.write("%d)" % formula.bv_extend_step())

    def walk_forall(self, formula: FNode):
        assert False, "not supported"
        return self.walk_quantifier("forall ", ", ", " . ", formula)

    def walk_exists(self, formula: FNode):
        assert False, "not supported"
        return self.walk_quantifier("exists ", ", ", " . ", formula)

    def walk_toreal(self, formula: FNode):
        assert isinstance(formula, FNode)
        self.write("((float)(")
        yield formula.arg(0)
        self.write("))")

    def walk_str_constant(self, formula: FNode):
        assert False, "not supported"
        assert (isinstance(formula.constant_value(), str)), \
            "The type was " + str(type(formula.constant_value()))
        self.write('"%s"' % formula.constant_value().replace('"', '""'))

    def walk_str_length(self, formula: FNode):
        assert False, "not supported"
        self.write("str.len(")
        self.walk(formula.arg(0))
        self.write(")")

    def walk_str_charat(self, formula: FNode, **kwargs):
        assert False, "not supported"
        self.write("str.at(")
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(")")

    def walk_str_concat(self, formula: FNode, **kwargs):
        assert False, "not supported"
        self.write("str.++(")
        for arg in formula.args()[:-1]:
            self.walk(arg)
            self.write(", ")
        self.walk(formula.args()[-1])
        self.write(")")

    def walk_str_contains(self, formula: FNode, **kwargs):
        assert False, "not supported"
        self.write("str.contains(")
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(")")

    def walk_str_indexof(self, formula: FNode, **kwargs):
        assert False, "not supported"
        self.write("str.indexof(")
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(", ")
        self.walk(formula.arg(2))
        self.write(")")

    def walk_str_replace(self, formula: FNode, **kwargs):
        assert False, "not supported"
        self.write("str.replace(")
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(", ")
        self.walk(formula.arg(2))
        self.write(")")

    def walk_str_substr(self, formula: FNode, **kwargs):
        assert False, "not supported"
        self.write("str.substr(")
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(", ")
        self.walk(formula.arg(2))
        self.write(")")

    def walk_str_prefixof(self, formula: FNode, **kwargs):
        assert False, "not supported"
        self.write("str.prefixof(")
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(")")

    def walk_str_suffixof(self, formula: FNode, **kwargs):
        assert False, "not supported"
        self.write("str.suffixof(")
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(")")

    def walk_str_to_int(self, formula: FNode, **kwargs):
        assert False, "not supported"
        self.write("str.to.int(")
        self.walk(formula.arg(0))
        self.write(")")

    def walk_int_to_str(self, formula: FNode, **kwargs):
        assert False, "not supported"
        self.write("int.to.str(")
        self.walk(formula.arg(0))
        self.write(")")

    def walk_array_store(self, formula: FNode):
        assert False, "not supported"
        yield formula.arg(0)
        self.write("[")
        yield formula.arg(1)
        self.write(" := ")
        yield formula.arg(2)
        self.write("]")

    def walk_array_value(self, formula: FNode):
        assert False, "not supported"
        self.write(str(self.env.stc.get_type(formula)))
        self.write("(")
        yield formula.array_value_default()
        self.write(")")
        assign = formula.array_value_assigned_values_map()
        # We sort the array value assigments in lexicographic order
        # for deterministic printing
        for k in sorted(assign, key=str):
            self.write("[")
            yield k
            self.write(" := ")
            yield assign[k]
            self.write("]")

    def walk_bv_tonatural(self, formula: FNode):
        assert False, "not supported"
        self.write("bv2nat(")
        yield formula.arg(0)
        self.write(")")

    def walk_bv_udiv(self, formula: FNode):
        assert False, "not supported"
        return self.walk_nary(formula, " u/ ")

    def walk_bv_urem(self, formula: FNode):
        assert False, "not supported"
        return self.walk_nary(formula, " u% ")

    def walk_bv_sdiv(self, formula: FNode):
        assert False, "not supported"
        return self.walk_nary(formula, " s/ ")

    def walk_bv_srem(self, formula: FNode):
        assert False, "not supported"
        return self.walk_nary(formula, " s% ")

    def walk_bv_sle(self, formula: FNode):
        assert False, "not supported"
        return self.walk_nary(formula, " s<= ")

    def walk_bv_slt(self, formula: FNode):
        assert False, "not supported"
        return self.walk_nary(formula, " s< ")

    def walk_bv_ule(self, formula: FNode):
        assert False, "not supported"
        return self.walk_nary(formula, " u<= ")

    def walk_bv_ult(self, formula: FNode):
        assert False, "not supported"
        return self.walk_nary(formula, " u< ")

    def walk_bv_lshl(self, formula: FNode):
        assert False, "not supported"
        return self.walk_nary(formula, " << ")

    def walk_bv_lshr(self, formula: FNode):
        assert False, "not supported"
        return self.walk_nary(formula, " >> ")

    def walk_bv_ashr(self, formula: FNode):
        assert False, "not supported"
        return self.walk_nary(formula, " a>> ")

    def walk_bv_comp(self, formula: FNode):
        assert False, "not supported"
        return self.walk_nary(formula, " bvcomp ")


class CPrinterReplace(CPrinter):
    """Like SMVPrinter but allows for replacing of subformulae.
    Longest expression is matched first (top-down in the three)
    """

    def __init__(self, stream: StringIO, subs: Optional[Dict[FNode, FNode]],
                 env: PysmtEnv = None):
        assert isinstance(stream, StringIO)
        assert env is None or isinstance(env, PysmtEnv)
        CPrinter.__init__(self, stream, env=env)
        self._subs = subs if subs else {}

    def printer(self, f: FNode, threshold=None) -> None:
        assert isinstance(f, FNode)
        self.walk(f, threshold=threshold)

    @handles(op.ALL_TYPES)
    def smart_walk(self, formula: FNode):
        assert isinstance(formula, FNode)
        if formula in self._subs:
            sub = self._subs[formula]
            self.write(sub)
        else:
            return CPrinter.super(self, formula)


class CSerializer(HRSerializer):
    PrinterClass = CPrinterReplace


def to_c(env: PysmtEnv, formula: FNode, subs: Optional[Dict[FNode, FNode]] = None,
         threshold: int = None):
    """Creates a SMVPrinterReplace with the given substitutions,
    transforms the given formula into a smv string and returns it"""
    buf = StringIO()
    p = CPrinterReplace(buf, subs=subs, env=env)
    p.printer(formula, threshold)
    res = buf.getvalue()
    buf.close()
    return res
