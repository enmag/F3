import io

from pysmt.environment import Environment as PysmtEnv
from pysmt.smtlib.script import smtlibscript_from_formula
from pysmt.logics import QF_NRA

_VERBOSE = 0


def set_verbosity(val: int):
    global _VERBOSE
    assert isinstance(val, int)
    _VERBOSE = val


def get_verbosity() -> int:
    global _VERBOSE
    return _VERBOSE


def log(msg: str, lvl: int = 5) -> None:
    assert isinstance(msg, str)
    if get_verbosity() >= lvl:
        print(msg, flush=__debug__)


def to_smt2(env: PysmtEnv, *formulas, logic=QF_NRA) -> str:
    assert isinstance(env, PysmtEnv)
    script = smtlibscript_from_formula(env.formula_manager.And(*formulas),
                                       logic=logic, env=env)
    with io.StringIO() as buf:
        script.serialize(buf, env=env)
        return buf.getvalue()
