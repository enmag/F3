import re
from io import StringIO

from pysmt.environment import Environment as PysmtEnv
from pysmt.printers import HRPrinter, HRSerializer
from pysmt.constants import is_pysmt_fraction
from pysmt.fnode import FNode
from pysmt.walkers.generic import handles
from pysmt.typing import PySMTType, INT, REAL, BOOL
import pysmt.operators as op

from smv_prefixes import NEXT_MONITOR_PREFIX


class SMVPrinter(HRPrinter):
    """Performs serialization of a formula in SMV format.
    E.g., Implies(And(Symbol(x), Symbol(y)), Symbol(z))  ~>   '(x * y) -> z'
    """

    def smvtype(self, pysmt_t) -> None:
        if pysmt_t.is_bool_type():
            self.write("boolean")
        elif pysmt_t.is_int_type():
            self.write("integer")
        else:
            assert pysmt_t.is_real_type(), str(pysmt_t)
            self.write("real")

    def __init__(self, stream: StringIO, env: PysmtEnv = None):
        assert env is None or isinstance(env, PysmtEnv)
        HRPrinter.__init__(self, stream, env=env)
        self.stream = stream
        self.write = self.stream.write
        self._next_op_re = re.compile(r"next(\S+)")

    def print_ltl(self, solver, enc, ltl):
        import mathsat
        assert not isinstance(ltl, FNode)

        menv = solver.msat_env()
        arity = mathsat.msat_term_arity(ltl)
        assert arity in {0, 1, 2}
        if arity == 0:
            assert not enc.is_ltl(ltl)
            ltl = solver.converter.back(ltl)
            return self.printer(ltl)
        args = [mathsat.msat_term_get_arg(ltl, i) for i in range(arity)]
        if enc.is_X(ltl):
            assert arity == 1
            self.write("(X ")
            self.print_ltl(solver, enc, args[0])
            self.write(")")
        elif enc.is_F(ltl):
            assert arity == 1
            self.write("(F ")
            self.print_ltl(solver, enc, args[0])
            self.write(")")
        elif enc.is_G(ltl):
            assert arity == 1
            self.write("(G ")
            self.print_ltl(solver, enc, args[0])
            self.write(")")
        elif enc.is_U(ltl):
            assert arity == 2
            self.write("(")
            self.print_ltl(solver, enc, args[0])
            self.write(" U ")
            self.print_ltl(solver, enc, args[1])
            self.write(")")
        elif mathsat.msat_term_is_and(menv, ltl):
            assert arity == 2
            self.write("(")
            self.print_ltl(solver, enc, args[0])
            self.write(" & ")
            self.print_ltl(solver, enc, args[1])
            self.write(")")
        elif mathsat.msat_term_is_or(menv, ltl):
            assert arity == 2
            self.write("(")
            self.print_ltl(solver, enc, args[0])
            self.write(" | ")
            self.print_ltl(solver, enc, args[1])
            self.write(")")
        elif mathsat.msat_term_is_iff(menv, ltl):
            assert arity == 2
            self.write("(")
            self.print_ltl(solver, enc, args[0])
            self.write(" <-> ")
            self.print_ltl(solver, enc, args[1])
            self.write(")")
        elif mathsat.msat_term_is_not(menv, ltl):
            assert arity == 1
            self.write("(! ")
            self.print_ltl(solver, enc, args[0])
            self.write(")")
        else:
            assert not enc.is_ltl(ltl)
            ltl = solver.converter.back(ltl)
            self.printer(ltl)

    def walk_symbol(self, formula: FNode) -> None:
        assert isinstance(formula, FNode)
        name = formula.symbol_name()
        if self._next_op_re.fullmatch(name):
            self.write(formula.symbol_name())
        elif name.startswith(NEXT_MONITOR_PREFIX):
            name = name[len(NEXT_MONITOR_PREFIX):]
            self.write(f"next({name})")
        else:
            HRPrinter.walk_symbol(self, formula)

    def walk_real_constant(self, formula: FNode) -> None:
        assert isinstance(formula, FNode)
        assert is_pysmt_fraction(formula.constant_value()), \
            "The type was " + str(type(formula.constant_value()))
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
            self.write(f"{sign}{n}.0")
        else:
            self.write(f"{sign}f'{n}/{d}")

    def walk_bool_constant(self, formula: FNode):
        assert isinstance(formula, FNode)
        if formula.constant_value():
            self.write("TRUE")
        else:
            self.write("FALSE")

    def walk_pow(self, formula: FNode):
        assert isinstance(formula, FNode)
        self.write("pow(")
        yield formula.arg(0)
        self.write(", ")
        yield formula.arg(1)
        self.write(")")

    def walk_array_select(self, formula: FNode):
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

    def walk_bv_constant(self, formula: FNode):
        # This is the simplest SMT-LIB way of printing the value of a BV
        # self.write("(_ bv%d %d)" % (formula.bv_width(),
        #                             formula.constant_value()))
        assert False, "not supported bv_constant: " \
            "`{}` `{}`".format(formula.constant_value(), formula.bv_width())
        self.write("0ub{}_{}".format(formula.bv_width(),
                                     formula.constant_value()))

    def walk_bv_ror(self, formula: FNode):
        assert False
        self.write("(")
        yield formula.arg(0)
        self.write(" ROR ")
        self.write("%d)" % formula.bv_rotation_step())

    def walk_bv_rol(self, formula: FNode):
        assert False
        self.write("(")
        yield formula.arg(0)
        self.write(" ROL ")
        self.write("%d)" % formula.bv_rotation_step())

    def walk_bv_zext(self, formula: FNode):
        assert False
        self.write("(")
        yield formula.arg(0)
        self.write(" ZEXT ")
        self.write("%d)" % formula.bv_extend_step())

    def walk_bv_sext(self, formula: FNode):
        assert False
        self.write("(")
        yield formula.arg(0)
        self.write(" SEXT ")
        self.write("%d)" % formula.bv_extend_step())

    def walk_forall(self, formula: FNode):
        assert False
        return self.walk_quantifier("forall ", ", ", " . ", formula)

    def walk_exists(self, formula: FNode):
        assert False
        return self.walk_quantifier("exists ", ", ", " . ", formula)

    def walk_toreal(self, formula: FNode):
        assert isinstance(formula, FNode)
        yield formula.arg(0)

    def walk_str_constant(self, formula: FNode):
        assert False
        assert (type(formula.constant_value()) == str), \
            "The type was " + str(type(formula.constant_value()))
        self.write('"%s"' % formula.constant_value().replace('"', '""'))

    def walk_str_length(self, formula: FNode):
        assert False
        self.write("str.len(")
        self.walk(formula.arg(0))
        self.write(")")

    def walk_str_charat(self, formula: FNode, **kwargs):
        assert False
        self.write("str.at(")
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(")")

    def walk_str_concat(self, formula: FNode, **kwargs):
        assert False
        self.write("str.++(")
        for arg in formula.args()[:-1]:
            self.walk(arg)
            self.write(", ")
        self.walk(formula.args()[-1])
        self.write(")")

    def walk_str_contains(self, formula: FNode, **kwargs):
        assert False
        self.write("str.contains(")
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(")")

    def walk_str_indexof(self, formula: FNode, **kwargs):
        assert False
        self.write("str.indexof(")
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(", ")
        self.walk(formula.arg(2))
        self.write(")")

    def walk_str_replace(self, formula: FNode, **kwargs):
        assert False
        self.write("str.replace(")
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(", ")
        self.walk(formula.arg(2))
        self.write(")")

    def walk_str_substr(self, formula: FNode, **kwargs):
        assert False
        self.write("str.substr(")
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(", ")
        self.walk(formula.arg(2))
        self.write(")")

    def walk_str_prefixof(self, formula: FNode, **kwargs):
        assert False
        self.write("str.prefixof(")
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(")")

    def walk_str_suffixof(self, formula: FNode, **kwargs):
        assert False
        self.write("str.suffixof(")
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(")")

    def walk_str_to_int(self, formula: FNode, **kwargs):
        assert False
        self.write("str.to.int(")
        self.walk(formula.arg(0))
        self.write(")")

    def walk_int_to_str(self, formula: FNode, **kwargs):
        assert False
        self.write("int.to.str(")
        self.walk(formula.arg(0))
        self.write(")")

    def walk_array_store(self, formula: FNode):
        assert False
        yield formula.arg(0)
        self.write("[")
        yield formula.arg(1)
        self.write(" := ")
        yield formula.arg(2)
        self.write("]")

    def walk_array_value(self, formula: FNode):
        assert False
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
        assert False
        self.write("bv2nat(")
        yield formula.arg(0)
        self.write(")")

    def walk_bv_udiv(self, formula: FNode):
        assert False
        return self.walk_nary(formula, " u/ ")

    def walk_bv_urem(self, formula: FNode):
        assert False
        return self.walk_nary(formula, " u% ")

    def walk_bv_sdiv(self, formula: FNode):
        assert False
        return self.walk_nary(formula, " s/ ")

    def walk_bv_srem(self, formula: FNode):
        assert False
        return self.walk_nary(formula, " s% ")

    def walk_bv_sle(self, formula: FNode):
        assert False
        return self.walk_nary(formula, " s<= ")

    def walk_bv_slt(self, formula: FNode):
        assert False
        return self.walk_nary(formula, " s< ")

    def walk_bv_ule(self, formula: FNode):
        assert False
        return self.walk_nary(formula, " u<= ")

    def walk_bv_ult(self, formula: FNode):
        assert False
        return self.walk_nary(formula, " u< ")

    def walk_bv_lshl(self, formula: FNode):
        assert False
        return self.walk_nary(formula, " << ")

    def walk_bv_lshr(self, formula: FNode):
        assert False
        return self.walk_nary(formula, " >> ")

    def walk_bv_ashr(self, formula: FNode):
        assert False
        return self.walk_nary(formula, " a>> ")

    def walk_bv_comp(self, formula: FNode):
        assert False
        return self.walk_nary(formula, " bvcomp ")


class SMVPrinterReplace(SMVPrinter):
    """Like SMVPrinter but allows for replacing of subformulae.
    Longest expression is matched first (top-down in the three)
    """

    def __init__(self, stream: StringIO, subs: dict, env: PysmtEnv):
        assert isinstance(stream, StringIO)
        assert isinstance(env, PysmtEnv)
        SMVPrinter.__init__(self, stream, env=env)
        self._subs = subs if subs else {}

    def printer(self, f: FNode, threshold=None):
        assert isinstance(f, FNode)
        self.walk(f, threshold=threshold)

    @handles(op.ALL_TYPES)
    def smart_walk(self, formula: FNode):
        assert isinstance(formula, FNode)
        if formula in self._subs:
            sub = self._subs[formula]
            self.write(sub)
        else:
            return SMVPrinter.super(self, formula)


class SMVSerializer(HRSerializer):
    PrinterClass = SMVPrinterReplace


def to_smv(env: PysmtEnv, formula: FNode, subs: dict = None,
           threshold: int = None) -> str:
    """Creates a SMVPrinterReplace with the given substitutions,
    transforms the given formula into a smv string and returns it"""
    assert isinstance(env, PysmtEnv)
    assert isinstance(formula, FNode)
    assert formula in env.formula_manager.formulae.values()

    with StringIO() as buf:
        p = SMVPrinterReplace(buf, subs=subs, env=env)
        p.printer(formula, threshold)
        return buf.getvalue()


def ltl_to_smv(env: PysmtEnv, solver, enc, ltl) -> str:
    with StringIO() as buf:
        p = SMVPrinter(buf, env=env)
        p.print_ltl(solver, enc, ltl)
        return buf.getvalue()


def smv_type(symb_sort: PySMTType) -> str:
    """Translate pysmt type into the corresponding smv type"""
    assert isinstance(symb_sort, PySMTType)
    res = ""
    if symb_sort == INT:
        res = "integer"
    elif symb_sort == REAL:
        res = "real"
    elif symb_sort == BOOL:
        res = "boolean"
    else:
        assert False, f"unknown type `{symb_sort}`"
    return res
