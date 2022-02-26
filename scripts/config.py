class Config:
    _nonterm_ls_dirs = frozenset(["software_nontermination"])
    _nonterm_ns_dirs = frozenset(["nonlinear_software"])
    _fltl_its_dirs = frozenset(["airbag", "bakery_simple_bug", "bounded_counter",
                                "semaphore", "simple_int_loops",
                                "simple_real_loops"])
    _fltl_maxp_dirs = frozenset(["maxplus"])
    _finvar_ta_dirs = frozenset(["ta_finvar_critical_region", "ta_finvar_csma",
                                 "ta_finvar_fddi", "ta_finvar_fischer",
                                 "ta_finvar_lynch", "ta_finvar_train"])
    _tinvar_ta_dirs = frozenset(["ta_tinvar_critical_region", "ta_tinvar_csma",
                                 "ta_tinvar_fddi", "ta_tinvar_fischer",
                                 "ta_tinvar_lynch", "ta_tinvar_train"])
    _fltl_ta_dirs = frozenset(["ta_fltl_critical_region", "ta_fltl_csma",
                               "ta_fltl_fddi", "ta_fltl_fischer",
                               "ta_fltl_lynch", "ta_fltl_train"])
    _tltl_ta_dirs = frozenset(["ta_tltl_critical_region", "ta_tltl_csma",
                               "ta_tltl_fddi", "ta_tltl_fischer",
                               "ta_tltl_lynch", "ta_tltl_train"])
    _fmtl_ta_dirs = frozenset(["ta_fmtl_critical_region", "ta_fmtl_csma",
                               "ta_fmtl_fddi", "ta_fmtl_fischer",
                               "ta_fmtl_lynch", "ta_fmtl_train"])
    _tmtl_ta_dirs = frozenset(["ta_tmtl_critical_region", "ta_tmtl_csma",
                               "ta_tmtl_fddi", "ta_tmtl_fischer",
                               "ta_tmtl_lynch", "ta_tmtl_train"])
    _fltl_tts_dirs = frozenset(["tts",
                                "tts_csma_backoff", "tts_dynamic_fischer",
                                "tts_dynamic_lynch", "tts_token_ring"])
    _fltl_hs_dirs = frozenset(["hybrid_system"])
    _fltl_hs_hints_dirs = frozenset(["hybrid_system_hints"])
    _hint_combs_dirs = frozenset(["wrong_hints_ltl_infinite_state",
                                  "wrong_hints_ltl_timed_transition_system",
                                  "wrong_hints_nonlinear_software",
                                  "wrong_hints_software"])
    _hint_perms_dirs = frozenset(
        ["wrong_hints_permutations_ltl_infinite_state",
         "wrong_hints_permutations_ltl_timed_transition_system",
         "wrong_hints_permutations_nonlinear_software",
         "wrong_hints_permutations_software"])
    all_dirs = frozenset.union(_nonterm_ls_dirs, _nonterm_ns_dirs,
                               _fltl_its_dirs, _fltl_maxp_dirs,
                               _finvar_ta_dirs, _tinvar_ta_dirs,
                               _fltl_ta_dirs, _tltl_ta_dirs,
                               _fmtl_ta_dirs, _tmtl_ta_dirs,
                               _fltl_tts_dirs, _fltl_hs_dirs,
                               _fltl_hs_hints_dirs,
                               _hint_combs_dirs, _hint_perms_dirs)

    def __init__(self, opts):
        self.nonterm_ls = opts.linear_software
        self.nonterm_ns = opts.nonlinear_software
        self.fltl_its = opts.inf_state_ts
        self.fltl_maxp = opts.max_plus
        self.tinvar_ta = opts.true_invar_timed_automata
        self.finvar_ta = opts.false_invar_timed_automata
        self.tltl_ta = opts.true_ltl_timed_automata
        self.fltl_ta = opts.false_ltl_timed_automata
        self.tmtl_ta = opts.true_mtl_timed_automata
        self.fmtl_ta = opts.false_mtl_timed_automata
        self.fltl_tts = opts.timed_transition_systems
        self.fltl_hs = opts.hybrid_systems
        self.fltl_hsh = opts.hybrid_systems_hints
        self.hint_combs = opts.comb_hints
        self.hint_perms = opts.perm_hints

        self.dirs = set()
        if self.nonterm_ls:
            self.dirs.update(Config._nonterm_ls_dirs)
        if self.nonterm_ls:
            self.dirs.update(Config._nonterm_ns_dirs)
        if self.fltl_its:
            self.dirs.update(Config._fltl_its_dirs)
        if self.fltl_maxp:
            self.dirs.update(Config._fltl_maxp_dirs)
        if self.tinvar_ta:
            self.dirs.update(Config._tinvar_ta_dirs)
        if self.finvar_ta:
            self.dirs.update(Config._finvar_ta_dirs)
        if self.tltl_ta:
            self.dirs.update(Config._tltl_ta_dirs)
        if self.fltl_ta:
            self.dirs.update(Config._fltl_ta_dirs)
        if self.tmtl_ta:
            self.dirs.update(Config._tmtl_ta_dirs)
        if self.fmtl_ta:
            self.dirs.update(Config._fmtl_ta_dirs)
        if self.fltl_tts:
            self.dirs.update(Config._fltl_tts_dirs)
        if self.fltl_hs:
            self.dirs.update(Config._fltl_hs_dirs)
        if self.fltl_hsh:
            self.dirs.update(Config._fltl_hs_hints_dirs)
        if self.hint_combs:
            self.dirs.update(Config._hint_combs_dirs)
        if self.hint_perms:
            self.dirs.update(Config._hint_perms_dirs)

    def is_dir2read(self, name) -> bool:
        return name in self.dirs

    def expected_res(self, name) -> bool:
        return name in frozenset.union(Config._tinvar_ta_dirs,
                                       Config._tltl_ta_dirs,
                                       Config._tmtl_ta_dirs)
