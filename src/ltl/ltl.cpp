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

#include "ltl.h"
#include <algorithm>


LTLEncoder::LTLEncoder(const Options &opts, msat_env env):
    opts_(opts),
    env_(env),
    vp_(env)
{
    MSAT_MAKE_ERROR_TERM(neg_f_);
    ltl_X_ = { nullptr };
    ltl_F_ = { nullptr };
    ltl_G_ = { nullptr };
    ltl_U_ = { nullptr };
    ltl_V_ = { nullptr };
    num_fairness_ = 0;
}


bool LTLEncoder::init()
{
    if (ltl_syms_.empty()) {
        msat_type btp = msat_get_bool_type(env_);
        std::vector<msat_type> tps = { btp };
        msat_type tp = msat_get_function_type(env_, &tps[0], tps.size(), btp);
        if (MSAT_ERROR_TYPE(tp)) {
            // logger(1) << "ERROR: this version of MathSAT doesn't support "
            //           << "the option -allow_bool_function_args=true, required"
            //           << "for LTL" << endlog;
            return false;
        }
        ltl_X_ = msat_declare_function(env_, "ltl_X", tp);
        ltl_F_ = msat_declare_function(env_, "ltl_F", tp);
        ltl_G_ = msat_declare_function(env_, "ltl_G", tp);
        tps.push_back(btp);
        tp = msat_get_function_type(env_, &tps[0], tps.size(), btp);
        ltl_U_ = msat_declare_function(env_, "ltl_U", tp);
        ltl_V_ = msat_declare_function(env_, "ltl_V", tp);

        ltl_syms_.insert(msat_decl_id(ltl_X_));
        ltl_syms_.insert(msat_decl_id(ltl_F_));
        ltl_syms_.insert(msat_decl_id(ltl_G_));
        ltl_syms_.insert(msat_decl_id(ltl_U_));
        ltl_syms_.insert(msat_decl_id(ltl_V_));
    }
    return true;
}


msat_term LTLEncoder::make_X(msat_term f, bool push)
{
    if (!push) {
        args_.clear();
        args_.push_back(f);
        return msat_make_term(env_, ltl_X_, &args_[0]);
    } else {
        struct Data {
            TermList &args;
            msat_decl ltl_X;
            TermMap cache;
        };
        auto visit =
            [](msat_env e, msat_term t, int pre, void *d) -> msat_visit_status
            {
                Data *data = static_cast<Data *>(d);
                msat_decl s = msat_term_get_decl(t);

                switch (msat_decl_get_tag(e, s)) {
                case MSAT_TAG_AND:
                case MSAT_TAG_OR:
                case MSAT_TAG_NOT:
                case MSAT_TAG_IFF:
                    if (!pre) {
                        data->args.clear();
                        for (size_t i = 0; i < msat_term_arity(t); ++i) {
                            auto c = data->cache[msat_term_get_arg(t, i)];
                            data->args.push_back(c);
                        }
                        data->cache[t] =
                            msat_make_term(e, s, &data->args[0]);
                    }
                    return MSAT_VISIT_PROCESS;
                default:
                    if (!pre) {
                        data->args = { t };
                        data->cache[t] =
                            msat_make_term(e, data->ltl_X, &data->args[0]);
                    }
                    return MSAT_VISIT_SKIP;
                }
            };

        Data d = { args_, ltl_X_ };
        msat_visit_term(env_, f, visit, &d);
        auto ret = d.cache[f];
        return ret;
    }
}


msat_term LTLEncoder::make_U(msat_term f1, msat_term f2)
{
    args_.clear();
    args_.push_back(f1);
    args_.push_back(f2);
    return msat_make_term(env_, ltl_U_, &args_[0]);
}


msat_term LTLEncoder::make_V(msat_term f1, msat_term f2)
{
    args_.clear();
    args_.push_back(f1);
    args_.push_back(f2);
    return msat_make_term(env_, ltl_V_, &args_[0]);
}


msat_term LTLEncoder::make_F(msat_term f)
{
    args_.clear();
    args_.push_back(f);
    return msat_make_term(env_, ltl_F_, &args_[0]);
}


msat_term LTLEncoder::make_G(msat_term f)
{
    args_.clear();
    args_.push_back(f);
    return msat_make_term(env_, ltl_G_, &args_[0]);
}


bool LTLEncoder::is_ltl(msat_term t) const
{
    int id = msat_decl_id(msat_term_get_decl(t));
    return ltl_syms_.find(id) != ltl_syms_.end();
}


bool LTLEncoder::is_X(msat_term t) const
{
    return msat_decl_id(msat_term_get_decl(t)) == msat_decl_id(ltl_X_);
}


bool LTLEncoder::is_U(msat_term t) const
{
    return msat_decl_id(msat_term_get_decl(t)) == msat_decl_id(ltl_U_);
}


bool LTLEncoder::is_V(msat_term t) const
{
    return msat_decl_id(msat_term_get_decl(t)) == msat_decl_id(ltl_V_);
}


bool LTLEncoder::is_F(msat_term t) const
{
    return msat_decl_id(msat_term_get_decl(t)) == msat_decl_id(ltl_F_);
}


bool LTLEncoder::is_G(msat_term t) const
{
    return msat_decl_id(msat_term_get_decl(t)) == msat_decl_id(ltl_G_);
}


TransitionSystem LTLEncoder::encode(const TermMap &statevars,
                                    const msat_term ltl)
{
    msat_term init = msat_make_true(env_);
    msat_term trans = msat_make_true(env_);
    TermList justice;
    TransitionSystem ts(env_);
    TermMap tssv;

    if (is_special_case(ltl, justice)) {
        // logger(1) << "special case detected: the property "
        //           << " is a conjunction of " << justice.size()
        //           << " fairness constraints" << endlog;
        neg_f_ = msat_make_not(env_, ltl);
        sat_[neg_f_] = msat_make_true(env_);
    } else {
        neg_f_ = normalize(msat_make_not(env_, ltl));
        get_elementary_subformulas(neg_f_);
        TermMap sv = statevars;
        for (auto p : el2f_) {
            msat_term v = p.first;
            msat_term n = vp_.fresh_var_pref(v, "_x_");
            sv[v] = n;
            nel2el_[n] = v;
        }
        trans = get_constraints(sv, neg_f_, justice);
        init = sat_[neg_f_];

        for (auto p : el2f_) {
            tssv[p.first] = sv[p.first];
        }
    }

    num_fairness_ = justice.size();
    make_single_justice(tssv, justice, init, trans);

    for (auto &j : justice) {
        j = msat_make_not(env_, j);
    }

    const bool ok = ts.initialize(tssv, init, trans, justice[0], true);
    assert(ok);

    return ts;
}


msat_term LTLEncoder::normalize(msat_term ltl)
{
    struct Data {
        LTLEncoder *enc;
        TermMap &cache;
        TermList &args;

        Data(LTLEncoder *e, TermMap &c, TermList &a):
            enc(e), cache(c), args(a) {}
    };

    auto visit =
        [](msat_env e, msat_term t, int pre, void *data) -> msat_visit_status
        {
            if (!pre) {
                Data *d = static_cast<Data *>(data);
                d->args.clear();
                msat_term tt;
                for (size_t i = 0; i < msat_term_arity(t); ++i) {
                    d->args.push_back(d->cache[msat_term_get_arg(t, i)]);
                }
                if (d->enc->is_F(t)) {
                    tt = d->enc->make_U(msat_make_true(e), d->args[0]);
                } else if (d->enc->is_G(t)) {
                    tt = msat_make_not(
                        e, d->enc->make_U(msat_make_true(e),
                                          msat_make_not(e, d->args[0])));
                } else if (d->enc->is_V(t)) {
                    tt = msat_make_not(
                        e, d->enc->make_U(msat_make_not(e, d->args[0]),
                                          msat_make_not(e, d->args[1])));
                // } else if (d->enc->is_X(t)) {
                //     tt = d->enc->make_X(d->args[0]); // push X to the leaves
                } else {
                    tt = msat_make_term(e, msat_term_get_decl(t), &d->args[0]);
                }
                d->cache[t] = tt;
            }
            return MSAT_VISIT_PROCESS;
        };

    TermMap cache;
    Data d(this, cache, args_);
    msat_visit_term(env_, ltl, visit, &d);

    msat_term ret = cache[ltl];

    // logger(4) << "normalized " << logterm(env_, ltl) << " into "
    //           << logterm(env_, ret) << endlog;
    return ret;
}


msat_term LTLEncoder::neg_prop_label() const
{
    msat_term ret;
    MSAT_MAKE_ERROR_TERM(ret);
    auto it = sat_.find(neg_f_);
    if (it != sat_.end()) {
        ret = it->second;
    }
    return ret;
}


bool LTLEncoder::is_special_case(msat_term ltl, TermList &justice)
{
    struct Data {
        LTLEncoder *enc;
        bool ok;
    };

    auto visit =
        [](msat_env e, msat_term t, int pre, void *data) -> msat_visit_status
        {
            if (pre) {
                Data *d = static_cast<Data *>(data);
                if (d->enc->is_ltl(t)) {
                    d->ok = false;
                    return MSAT_VISIT_ABORT;
                }
            }
            return MSAT_VISIT_PROCESS;
        };

    if (!msat_term_is_not(env_, ltl)) {
        return false;
    }

    TermHashSet seen;
    TermList to_process = { msat_term_get_arg(ltl, 0) };
    while (!to_process.empty()) {
        auto t = to_process.back();
        to_process.pop_back();
        if (!seen.insert(t).second) {
            continue;
        }
        if (msat_term_is_and(env_, t)) {
            to_process.push_back(msat_term_get_arg(t, 1));
            to_process.push_back(msat_term_get_arg(t, 0));
        } else if (is_G(t) && is_F(msat_term_get_arg(t, 0))) {
            Data data = { this, true };
            auto fair = msat_term_get_arg(msat_term_get_arg(t, 0), 0);
            msat_visit_term(env_, fair, visit, &data);
            if (!data.ok) {
                return false;
            }
            justice.push_back(fair);
        } else {
            return false;
        }
    }

    return true;
}


void LTLEncoder::get_elementary_subformulas(msat_term neg_f)
{
    struct Data {
        LTLEncoder *enc;
        TermMap &f2el;
        TermMap &el2f;
        VarProvider &vp;

        Data(LTLEncoder *e, TermMap &a, TermMap &b, VarProvider &v):
            enc(e), f2el(a), el2f(b), vp(v) {}

        msat_term make_el(msat_term t)
        {
            return vp.fresh_var(std::string("EL_") +
                                (enc->is_U(t) ? "U_" : "X_") +
                                std::to_string(msat_term_id(t)));
        }
    };

    auto visit =
        [](msat_env e, msat_term t, int pre, void *data) -> msat_visit_status
        {
            if (!pre) {
                Data *d = static_cast<Data *>(data);
                if (d->enc->is_X(t) || d->enc->is_U(t)) {
                    msat_term l = d->make_el(t);
                    msat_term tt = t;
                    if (d->enc->is_U(t)) {
                        tt = d->enc->make_X(t);
                    }
                    d->f2el[t] = l;
                    d->el2f[l] = tt;
                }
            }
            return MSAT_VISIT_PROCESS;
        };

    Data d(this, f2el_, el2f_, vp_);
    msat_visit_term(env_, neg_f, visit, &d);
}


msat_term LTLEncoder::get_constraints(const TermMap &statevars,
                                      msat_term neg_f, TermList &justice)
{
#ifndef NDEBUG
    for (auto p : statevars) {
        assert(!MSAT_ERROR_TERM(p.first));
        assert(!MSAT_ERROR_TERM(p.second));
    }
#endif

    struct Data {
        LTLEncoder *enc;
        const TermMap &sv;
        TermMap &f2el;
        TermMap &sat;
        TermList &justice;
        TermList &args;
        std::vector<UntilRule> &until_rules;
        std::vector<NextRule> &next_rules;
        TermList trans;
        TermMap cache;

        Data(LTLEncoder *e, const TermMap &st,
             TermMap &m, TermMap &s, TermList &j, TermList &a,
             std::vector<UntilRule> &r, std::vector<NextRule> &n):
            enc(e), sv(st), f2el(m), sat(s), justice(j), args(a),
            until_rules(r), next_rules(n) {}

        msat_term next(msat_env e, msat_term t)
        {
            auto func =
                [&](msat_term t) -> msat_term
                {
                    auto it = sv.find(t);
                    if (it != sv.end()) {
                        msat_term r = it->second;
                        assert(!MSAT_ERROR_TERM(r));
                        return r;
                    }
                    return t;
                };
            return apply_substitution(e, t, cache, func);
        }
    };

    auto visit =
        [](msat_env e, msat_term t, int pre, void *data) -> msat_visit_status
        {
            if (!pre) {
                Data *d = static_cast<Data *>(data);
                d->args.clear();
                for (size_t i = 0; i < msat_term_arity(t); ++i) {
                    d->args.push_back(d->sat[msat_term_get_arg(t, i)]);
                }
                if (d->enc->is_X(t)) {
                    msat_term el = d->f2el[t];
                    d->sat[t] = el;
                    msat_term n = d->next(e, d->args[0]);
                    d->trans.push_back(msat_make_eq(e, el, n));
                    d->next_rules.push_back({t, el, d->args[0]});
                } else if (d->enc->is_U(t)) {
                    msat_term el = d->f2el[t];
                    msat_term f =
                        msat_make_or(e, d->args[1],
                                     msat_make_and(e, d->args[0], el));
                    d->sat[t] = f;
                    msat_term n = d->next(e, f);
                    d->trans.push_back(msat_make_eq(e, el, n));
                    d->until_rules.push_back({t, el, d->args[0], d->args[1]});
                    d->justice.push_back(msat_make_or(e, msat_make_not(e, f),
                                                      d->args[1]));
                } else {
                    msat_term tt = msat_make_term(e, msat_term_get_decl(t),
                                                  &d->args[0]);
                    d->sat[t] = tt;
                }
            }
            return MSAT_VISIT_PROCESS;
        };

    Data d(this, statevars, f2el_, sat_, justice, args_,
           until_rules_, next_rules_);
    msat_visit_term(env_, neg_f, visit, &d);

    msat_term trans = make_and(env_, d.trans);
    return trans;
}


const std::vector<UntilRule> &LTLEncoder::until_rules() const
{
    return until_rules_;
}


const std::vector<NextRule> &LTLEncoder::next_rules() const
{
    return next_rules_;
}


void LTLEncoder::make_single_justice(TermMap &sv, TermList &justice,
                                     msat_term &init, msat_term &trans)
{
    if (justice.size() == 1) {
        return;
    }

    std::sort(justice.begin(), justice.end());
    //std::random_shuffle(justice.begin(), justice.end());

    msat_term accept = msat_make_true(env_);
    fair2hist_.clear();

    for (auto j : justice) {
        auto l = vp_.fresh_var(std::string("J") +
                               std::to_string(msat_term_id(j)));
        fair2hist_.emplace_back(std::make_pair(j, l));
        auto n = vp_.fresh_var_pref(l, "_x_");
        sv[l] = n;

        init = msat_make_and(env_, init, msat_make_not(env_, l));
        accept = msat_make_and(env_, accept, l);
    }

    for (size_t i = 0; i < justice.size(); ++i) {
        auto j = justice[i];

        msat_term ok = msat_make_true(env_);
        if (opts_.ltl_single_fairness_sorted || opts_.check_witness) {
            for (size_t k = 0; k < i; ++k) {
                auto l = fair2hist_[k].second;
                ok = msat_make_and(env_, ok, l);
            }
        }

        auto l = fair2hist_[i].second;
        auto n = sv[l];

        trans = msat_make_and(
            env_, trans,
            msat_make_eq(env_, n,
                         make_ite(env_, accept, msat_make_false(env_),
                                  make_ite(env_,
                                           msat_make_and(env_, ok, j),
                                           msat_make_true(env_), l))));
                                           // msat_make_or(env_, j, l), l))));
    }

    // logger(1) << "combined " << justice.size() << " fairness constraints "
    //           << "into a single one" << endlog;

    justice.clear();
    justice.push_back(accept);
}


bool LTLEncoder::is_label(msat_term t) const
{
    return el2f_.find(t) != el2f_.end();
}


msat_term LTLEncoder::get_temporal_formula(msat_term lbl)
{
    msat_term ret;
    MSAT_MAKE_ERROR_TERM(ret);

    TermMap cache;
    // TermList args;
    // TermList to_process = { lbl };

    // while (!to_process.empty()) {
    //     auto t = to_process.back();
    //     if (cache.find(t) != cache.end()) {
    //         to_process.pop_back();
    //         continue;
    //     }

    //     auto it = nel2el_.find(t);
    //     if (it != nel2el_.end()) {
    //         auto tt = it->second;
    //         if (cache.find(tt) == cache.end()) {
    //             to_process.push_back(tt);
    //         } else {
    //             to_process.pop_back();
    //             cache[t] = make_X(cache[tt]);
    //         }
    //         continue;
    //     }

    //     it = el2f_.find(t);
    //     if (it != el2f_.end()) {
    //         auto tt = it->second;
    //         if (cache.find(tt) == cache.end()) {
    //             to_process.push_back(tt);
    //         } else {
    //             to_process.pop_back();
    //             cache[t] = cache[tt];
    //         }
    //         continue;
    //     }

    //     bool done = true;
    //     args.clear();
    //     for (size_t i = 0; i < msat_term_arity(t); ++i) {
    //         auto c = msat_term_get_arg(t, i);
    //         it = cache.find(c);
    //         if (it != cache.end()) {
    //             args.push_back(it->second);
    //         } else {
    //             done = false;
    //             to_process.push_back(c);
    //         }
    //     }

    //     if (done) {
    //         to_process.pop_back();
    //         auto tt = msat_make_term(env_, msat_term_get_decl(t), &args[0]);
    //         cache[t] = tt;
    //     }
    // }

    // ret = cache[lbl];
    // return ret;

    const auto subst =
        [&](msat_term v) -> msat_term
        {
            auto it = nel2el_.find(v);
            if (it != nel2el_.end()) {
                v = it->second;
                v = get_temporal_formula(v);
                v = make_X(v);
            }
            return v;
        };

    auto it = el2f_.find(lbl);
    if (it != el2f_.end()) {
        ret = apply_substitution(env_, it->second, cache, subst);
    }

    return ret;
}
