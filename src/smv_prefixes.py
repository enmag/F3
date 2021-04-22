NEXT_MONITOR_PREFIX = "_x_"

# automaton location
LOC_VAR = "_loc"
LOC_ID_PREFIX = "_l"
LOOPBACK_LOC_VAR = "_loopback_loc"

# labels on transitions
TRANS_LABEL = "_trans"

# helpers for l2s
IN_LOOP = "_in_loop"
FAIR_LOOP = "_fair_loop"
LOOPBACK = "_loopback"

IS_PREFIX = "_is_prefix"
PREFIX_LENGTH = "_prefix_length"
ACTIVE = "_active"
ENABLED = "_enabled"
SYMB_MASK = "_symbols_mask"

# fairness
FAIR_MASK = "_fairness_mask"
FAIR = "_fair"
FAIR_PRED = "_fair_pred"
N_FAIR_PRED = "_not_fair_pred"

# transition under-approximation
UAPPR_MASK = "_underapprox_mask"
UAPPR = "_underapproximate"
UAPPR_PRED = "_underappr_pred"
N_UAPPR_PRED = "_not_underappr_pred"

# prefix for module instance
MODULE_INST_PREF = "_i"

# prop names
PROP_FIND_LOOP = "FIND_FAIR_LOOP"
PROP_FIND_ANY_LOOP = "FIND_ANY_LOOP"
PROP_CHECK_UAPPR = "CHECK_IS_UNDERAPPROXIMATION"
PROP_CHECK_FAIR = "CHECK_FAIRNESS"
PROP_REACH = "CHECK_REACHABILITY"
PROP_SAT_UAPPR = "UNSAT_UNDERAPPROXIMATION"
