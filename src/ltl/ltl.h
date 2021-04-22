/** -*- C++ -*-
 *
 * LTL encoding
 * author: Alberto Griggio <griggio@fbk.eu>
 *
 * This file is part of ic3ia.
 * Copyright (C) 2018 Fondazione Bruno Kessler.
 *
 * ic3ia is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * ic3ia is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with ic3ia.  If not, see <http://www.gnu.org/licenses/>.
 */

#pragma once

#include "ts.h"
#include "utils.h"
#include "opts.h"

struct UntilRule {
  msat_term until;
  msat_term lbl;
  msat_term arg0;
  msat_term arg1;
};


struct NextRule {
  msat_term next;
  msat_term lbl;
  msat_term arg;
};


class LTLEncoder {
public:

    LTLEncoder(const Options &opts, msat_env env);
    bool init();

    msat_term make_X(msat_term f, bool push=true);
    msat_term make_U(msat_term f1, msat_term f2);
    msat_term make_F(msat_term f);
    msat_term make_G(msat_term f);
    msat_term make_V(msat_term f1, msat_term f2);

    bool is_ltl(msat_term t) const;
    bool is_X(msat_term t) const;
    bool is_U(msat_term t) const;
    bool is_F(msat_term t) const;
    bool is_G(msat_term t) const;
    bool is_V(msat_term t) const;

    TransitionSystem encode(const TermMap &statevars, const msat_term ltl);

    bool is_label(msat_term t) const;
    msat_term get_temporal_formula(msat_term lbl);

    msat_term normalize(msat_term ltl);
    msat_term neg_prop_label() const;
    const TermPairList &fairness_vars() const { return fair2hist_; }
    size_t num_fairness_constraints() const { return num_fairness_; }

    const std::vector<UntilRule> &until_rules() const;
    const std::vector<NextRule> &next_rules() const;

private:
    void get_elementary_subformulas(msat_term neg_f);
    void make_single_justice(TermMap &sv, TermList &justice,
                             msat_term &init, msat_term &trans);
    msat_term get_constraints(const TermMap &statevars,
                              msat_term neg_f, TermList &justice);
    bool is_special_case(msat_term ltl, TermList &justice);

    const Options &opts_;
    msat_env env_;
    VarProvider vp_;
    TermMap sat_;
    TermMap f2el_;
    TermMap el2f_;
    TermMap nel2el_;
    TermPairList fair2hist_;
    msat_term neg_f_;
    size_t num_fairness_;

    std::vector<UntilRule> until_rules_;
    std::vector<NextRule> next_rules_;

    msat_decl ltl_X_;
    msat_decl ltl_U_;
    msat_decl ltl_F_;
    msat_decl ltl_G_;
    msat_decl ltl_V_;
    std::unordered_set<int> ltl_syms_;

    TermList args_;
};
