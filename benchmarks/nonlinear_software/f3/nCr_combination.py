import pysmt.typing as types
from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
from utils import symb_to_next


def transition_system(env: PysmtEnv) -> (frozenset, FNode, FNode, FNode):
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    den = mgr.Symbol("den", types.INT)
    dmul = mgr.Symbol("dmul", types.INT)
    nCr = mgr.Symbol("nCr", types.INT)
    n_num = mgr.Symbol("n_num", types.INT)
    nmul = mgr.Symbol("nmul", types.INT)
    num = mgr.Symbol("num", types.INT)
    pc = mgr.Symbol("pc", types.INT)
    r_num = mgr.Symbol("r_num", types.INT)
    x_den = symb_to_next(mgr, den)
    x_dmul = symb_to_next(mgr, dmul)
    x_nCr = symb_to_next(mgr, nCr)
    x_n_num = symb_to_next(mgr, n_num)
    x_nmul = symb_to_next(mgr, nmul)
    x_num = symb_to_next(mgr, num)
    x_pc = symb_to_next(mgr, pc)
    x_r_num = symb_to_next(mgr, r_num)
    symbols = frozenset([den, dmul, nCr, n_num, nmul, num, pc, r_num])

    n_locs = 25
    int_bound = n_locs
    pcs = []
    x_pcs = []
    ints = [mgr.Int(i) for i in range(int_bound)]

    for l in range(n_locs):
        n = ints[l]
        pcs.append(mgr.Equals(pc, n))
        x_pcs.append(mgr.Equals(x_pc, n))

    m_1 = mgr.Int(-1)
    pcend = mgr.Equals(pc, m_1)
    x_pcend = mgr.Equals(x_pc, m_1)

    # initial location.
    init = pcs[0]

    # control flow graph.
    cfg = mgr.And(
        # pc = -1 : -1,
        mgr.Implies(pcend, x_pcend),
        # pc = 0 & !(n_num >= 1) : -1,
        mgr.Implies(mgr.And(pcs[0], mgr.Not(mgr.GE(n_num, ints[1]))), x_pcend),
        # pc = 0 & n_num >= 1 : 1,
        mgr.Implies(mgr.And(pcs[0], mgr.GE(n_num, ints[1])), x_pcs[1]),
        # pc = 1 : 2,
        mgr.Implies(pcs[1], x_pcs[2]),
        # pc = 2 : 3,
        mgr.Implies(pcs[2], x_pcs[3]),
        # pc = 3 : 4,
        mgr.Implies(pcs[3], x_pcs[4]),
        # pc = 4 : 5,
        mgr.Implies(pcs[4], x_pcs[5]),
        # pc = 5 : 6,
        mgr.Implies(pcs[5], x_pcs[6]),
        # pc = 6 & n_num >= r_num : 7,
        mgr.Implies(mgr.And(pcs[6], mgr.GE(n_num, r_num)), x_pcs[7]),
        # pc = 6 & !(n_num >= r_num) : 24,
        mgr.Implies(mgr.And(pcs[6], mgr.Not(mgr.GE(n_num, r_num))), x_pcs[24]),
        # pc = 7 : {8, 11},
        mgr.Implies(pcs[7], mgr.Or(x_pcs[8], x_pcs[11])),
        # pc = 8 & !(num < 1) : -1,
        mgr.Implies(mgr.And(pcs[8], mgr.Not(mgr.LT(num, ints[1]))), x_pcend),
        # pc = 8 & num < 1 : 9,
        mgr.Implies(mgr.And(pcs[8], mgr.LT(num, ints[1])), x_pcs[9]),
        # pc = 9 : 10,
        mgr.Implies(pcs[9], x_pcs[10]),
        # pc = 10 : -1,
        mgr.Implies(pcs[10], x_pcend),
        # pc = 11 & !(nCr >= 1) : 20,
        mgr.Implies(mgr.And(pcs[11], mgr.Not(mgr.GE(nCr, ints[1]))),
                    x_pcs[20]),
        # pc = 11 & nCr >= 1 : 12,
        mgr.Implies(mgr.And(pcs[11], mgr.GE(nCr, ints[1])), x_pcs[12]),
        # pc = 12 : {13, 16},
        mgr.Implies(pcs[12], mgr.Or(x_pcs[13], x_pcs[16])),
        # pc = 13 & !(num < 1) : -1,
        mgr.Implies(mgr.And(pcs[13], mgr.Not(mgr.LT(num, ints[1]))), x_pcend),
        # pc = 13 & num < 1 : 14,
        mgr.Implies(mgr.And(pcs[13], mgr.LT(num, ints[1])), x_pcs[14]),
        # pc = 14 : 15,
        mgr.Implies(pcs[14], x_pcs[15]),
        # pc = 15 : -1,
        mgr.Implies(pcs[15], x_pcend),
        # pc = 16 : 17,
        mgr.Implies(pcs[16], x_pcs[17]),
        # pc = 17 : 18,
        mgr.Implies(pcs[17], x_pcs[18]),
        # pc = 18 : 19,
        mgr.Implies(pcs[18], x_pcs[19]),
        # pc = 19 : 11,
        mgr.Implies(pcs[19], x_pcs[11]),
        # pc = 20 : {-1, 21},
        mgr.Implies(pcs[20], mgr.Or(x_pcend, x_pcs[21])),
        # pc = 21 & !(num < 1) : -1,
        mgr.Implies(mgr.And(pcs[21], mgr.Not(mgr.LT(num, ints[1]))), x_pcend),
        # pc = 21 & num < 1 : 22,
        mgr.Implies(mgr.And(pcs[21], mgr.LT(num, ints[1])), x_pcs[22]),
        # pc = 22 : 23,
        mgr.Implies(pcs[22], x_pcs[23]),
        # pc = 23 : -1,
        mgr.Implies(pcs[23], x_pcend),
        # pc = 24 : -1,
        mgr.Implies(pcs[24], x_pcend))

    # transition labels.
    labels = mgr.And(
        # (pc = -1 & pc' = -1) -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcend, x_pcend),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 0 & pc' = -1)  -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[0], x_pcend),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 0 & pc' = 1)   -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[0], x_pcs[1]),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 1 & pc' = 2)   -> (n_num' = n_num & num' = 1 & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[1], x_pcs[2]),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, ints[1]),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 2 & pc' = 3)   -> (n_num' = n_num & num' = num & den' = 1 & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[2], x_pcs[3]),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, ints[1]), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 3 & pc' = 4)   -> (n_num' = n_num & num' = num & den' = den & nmul' = n_num & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[3], x_pcs[4]),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, n_num),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 4 & pc' = 5)   -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = r_num & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[4], x_pcs[5]),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, r_num), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 5 & pc' = 6)   -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = 1),
        mgr.Implies(
            mgr.And(pcs[5], x_pcs[6]),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, ints[1]))),
        # (pc = 6 & pc' = 7)   -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[6], x_pcs[7]),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 6 & pc' = 24)  -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[6], x_pcs[24]),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 7 & pc' = 8)   -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[7], x_pcs[8]),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 7 & pc' = 11)  -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[7], x_pcs[11]),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 8 & pc' = -1)  -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[8], x_pcend),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 8 & pc' = 9)   -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[8], x_pcs[9]),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 9 & pc' = 10)  -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = num/den),
        mgr.Implies(
            mgr.And(pcs[9], x_pcs[10]),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, mgr.Div(num, den)))),
        # (pc = 10 & pc' = -1) -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[10], x_pcend),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 11 & pc' = 20) -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[11], x_pcs[20]),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 11 & pc' = 12) -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[11], x_pcs[12]),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 12 & pc' = 13) -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[12], x_pcs[13]),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 12 & pc' = 16) -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[12], x_pcs[16]),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 13 & pc' = -1) -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[13], x_pcend),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 13 & pc' = 14) -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[13], x_pcs[14]),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 14 & pc' = 15) -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = num/den),
        mgr.Implies(
            mgr.And(pcs[14], x_pcs[15]),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, mgr.Div(num, den)))),
        # (pc = 15 & pc' = -1) -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[15], x_pcend),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 16 & pc' = 17) -> (n_num' = n_num & num' = num*nmul & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[16], x_pcs[17]),
            mgr.And(mgr.Equals(x_n_num, n_num),
                    mgr.Equals(x_num, mgr.Times(num, nmul)),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 17 & pc' = 18) -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul-1 & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[17], x_pcs[18]),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den),
                    mgr.Equals(x_nmul, mgr.Minus(nmul, ints[1])),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 18 & pc' = 19) -> (n_num' = n_num & num' = num & den' = den*dmul & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[18], x_pcs[19]),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, mgr.Times(den, dmul)),
                    mgr.Equals(x_nmul, nmul), mgr.Equals(x_dmul, dmul),
                    mgr.Equals(x_r_num, r_num), mgr.Equals(x_nCr, nCr))),
        # (pc = 19 & pc' = 11) -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul-1 & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[19], x_pcs[11]),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, mgr.Minus(dmul, ints[1])),
                    mgr.Equals(x_r_num, r_num), mgr.Equals(x_nCr, nCr))),
        # (pc = 20 & pc' = -1) -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[20], x_pcend),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 20 & pc' = 21) -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[20], x_pcs[21]),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 21 & pc' = -1) -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[21], x_pcend),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 21 & pc' = 22) -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[21], x_pcs[22]),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 22 & pc' = 23) -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = num/den),
        mgr.Implies(
            mgr.And(pcs[22], x_pcs[23]),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, mgr.Div(num, den)))),
        # (pc = 23 & pc' = -1) -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[23], x_pcend),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))),
        # (pc = 24 & pc' = -1) -> (n_num' = n_num & num' = num & den' = den & nmul' = nmul & dmul' = dmul & r_num' = r_num & nCr' = nCr),
        mgr.Implies(
            mgr.And(pcs[24], x_pcend),
            mgr.And(mgr.Equals(x_n_num, n_num), mgr.Equals(x_num, num),
                    mgr.Equals(x_den, den), mgr.Equals(x_nmul, nmul),
                    mgr.Equals(x_dmul, dmul), mgr.Equals(x_r_num, r_num),
                    mgr.Equals(x_nCr, nCr))))

    # transition relation.
    trans = mgr.And(cfg, labels)

    # fairness.
    fairness = mgr.Not(pcend)

    return symbols, init, trans, fairness
