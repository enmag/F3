/** -*- C++ -*-
 *
 * Basic utils and definitions
 * author: Alberto Griggio <griggio@fbk.eu>
 *
 * This file is part of ic3ia.
 * Copyright (C) 2015-2016 Fondazione Bruno Kessler.
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

#include "mathsat.h"
#include "typedefs.h"
#include <assert.h>
#include <sstream>
#include <iostream>
#include <chrono>
#include <stdint.h>
#include <random>


// equality predicates and hash functions for msat_termS

inline bool operator==(msat_term a, msat_term b)
{
    return msat_term_id(a) == msat_term_id(b);
}

inline bool operator!=(msat_term a, msat_term b)
{
    return !(a == b);
}

inline bool operator<(msat_term a, msat_term b)
{
    return msat_term_id(a) < msat_term_id(b);
}

namespace std {

template<>
struct hash<::msat_term> {
    size_t operator()(::msat_term t) const { return msat_term_id(t); }
};

} // namespace std


// replacement for std::shuffle, to ensure repeatabiliy. (The implementation
// of std::shuffle is different across different standard libraries!)
// template <class T, class RNG>
// void shuffle(std::vector<T> &v, RNG &&g)
// {
//     if (v.empty()) {
//         return;
//     }

//     for (size_t i = 1; i < v.size(); ++i) {
//         std::uniform_int_distribution<decltype(i)> d(0, i);
//         std::swap(v[i], v[d(g)]);
//     }
// }


/**
 * Destructor class for msat_env
 */
// class EnvDeleter {
// public:
//     EnvDeleter(msat_env env): env_(env) {}
//     ~EnvDeleter()
//     {
//         if (!MSAT_ERROR_ENV(env_)) {
//             msat_destroy_env(env_);
//         }
//     }

// private:
//     msat_env env_;
// };



// convenience methods for dealing with literals represented as msat_termS

/** return the variable associated with the input literal l */
// inline msat_term var(msat_env e, msat_term l)
// {
//     while (msat_term_is_not(e, l)) {
//         l = msat_term_get_arg(l, 0);
//     }
//     return l;
// }

/** build a literal out of a term and a sign */
// inline msat_term lit(msat_env e, msat_term t, bool neg)
// {
//     return neg ? msat_term(msat_make_not(e, t)) : t;
// }

/** get the sign flag of the input literal l */
// inline bool negated(msat_env e, msat_term l)
// {
//     return l != var(e, l);
// }


// inline msat_term make_eq(msat_env e, msat_term a, msat_term b)
// {
//     if (msat_is_bool_type(e, msat_term_get_type(a))) {
//         return msat_make_iff(e, a, b);
//     } else {
//         return msat_make_equal(e, a, b);
//     }
// }

// template<class T> inline msat_term make_number(msat_env e, T num)
// {
//     std::ostringstream ss;
//     ss << num;
//     std::string num_str = ss.str();
//     return msat_make_number(e, num_str.c_str());
// }


/** generate a suitable configuration for MathSAT, given the input options */
// enum ModelGeneration {
//     NO_MODEL,
//     BOOL_MODEL,
//     FULL_MODEL
// };
// msat_config get_config(ModelGeneration model=NO_MODEL,
//                        bool interpolation=false, bool approx=false);


/**
 * Apply a substitution to an arbitrary term. cache is used for
 * memoization. func is a unary function invoked on every variable occurring
 * in the input term (that is not already in the cache), which must return the
 * substitution for the variable
 */
template <class Func>
msat_term apply_substitution(msat_env env, msat_term term, TermMap &cache,
                             Func subst)
{
    struct Data {
        Func subst;
        TermMap &cache;
        TermList args;

        Data(Func s, TermMap &c): subst(s), cache(c) {}
    };

    auto visit =
        [](msat_env e, msat_term t, int preorder,
           void *data) -> msat_visit_status
        {
            Data *d = static_cast<Data *>(data);

            if (d->cache.find(t) != d->cache.end()) {
                // cache hit
                assert(!MSAT_ERROR_TERM(d->cache[t]));

                return MSAT_VISIT_SKIP;
            }

            if (!preorder) {
                msat_term v;
                msat_decl s = msat_term_get_decl(t);
                if (msat_term_arity(t) == 0 &&
                    msat_decl_get_tag(e, s) == MSAT_TAG_UNKNOWN &&
                    !msat_term_is_number(e, t)) {
                    // t is a variable: get the substitution from the
                    // user-provided function
                    v = d->subst(t);
                } else {
                    // t is not a variable: build the result term from the
                    // results of its children
                    TermList &args = d->args;
                    args.clear();
                    //args.reserve(msat_term_arity(t));
                    for (size_t i = 0; i < msat_term_arity(t); ++i) {
                        msat_term c = msat_term_get_arg(t, i);
                        assert(d->cache.find(c) != d->cache.end());
                        msat_term cc = d->cache[c];
                        assert(!MSAT_ERROR_TERM(cc));
                        args.push_back(cc);
                    }
                    v = msat_make_term(e, s, &args[0]);
                }

                assert(!MSAT_ERROR_TERM(v));
                d->cache[t] = v;
            }

            return MSAT_VISIT_PROCESS;
        };
    Data data(subst, cache);
    msat_visit_term(env, term, visit, &data);

    return cache[term];
}


/**
 * A class for generating fresh variables in a given MathSAT environment
 */
class VarProvider {
public:
    explicit VarProvider(msat_env env):
        env_(env), id_(1) {}

    /**
     * generate a fresh variable of the given type. name is used for
     * debugging/display purposes: if not NULL, the symbol for new variable
     * will be ".name.ID", where ID is a numeric ID
     */
  msat_term fresh_var(const std::string &name, msat_type tp)
    {
        buf_.str("");
        if (name.empty()) {
            buf_ << "_fresh_";
        } else if (name[0] == '_') {
            buf_ << name;
        } else {
            buf_ << "_" << name;
        }
        auto p = buf_.tellp();
        std::string s;
        while (true) {
            s = buf_.str();
            msat_decl d = msat_find_decl(env_, s.c_str());
            if (MSAT_ERROR_DECL(d)) {
                break;
            }
            buf_.seekp(p);
            buf_ << (id_++);
        }
        msat_decl d = msat_declare_function(env_, s.c_str(), tp);
        return msat_make_constant(env_, d);
    }

    msat_term fresh_var(const std::string &name=std::string())
    {
        return fresh_var(name, msat_get_bool_type(env_));
    }

    msat_term fresh_var(msat_term base,
                        const std::string &suffix=std::string())
    {
        msat_decl d = msat_term_get_decl(base);
        char *n = msat_decl_get_name(d);
        std::string name(n);
        msat_free(n);
        if (!suffix.empty()) {
            name += suffix;
        }
        return fresh_var(name.c_str(), msat_term_get_type(base));
    }

  msat_term fresh_var_pref(msat_term base,
                           const std::string &prefix=std::string())
    {
      msat_decl d = msat_term_get_decl(base);
      char *n = msat_decl_get_name(d);
      std::string name(prefix);
      name.append(n);
      msat_free(n);
      return fresh_var(name.c_str(), msat_term_get_type(base));
    }


private:
    msat_env env_;
    unsigned int id_;
    std::stringstream buf_;
};


/**
 * Helper class for measuring time elapses
 */
// class TimeKeeper {
//     typedef std::chrono::time_point<std::chrono::steady_clock> Time;
// public:
//     inline TimeKeeper(double &out):
//         out_(out)
//     {
//         reset();
//     }

//     inline ~TimeKeeper()
//     {
//         out_ = get();
//     }

//     inline double get()
//     {
//         Time e = std::chrono::steady_clock::now();
//         std::chrono::duration<double> diff = e - start_;
//         return out_ + diff.count();
//     }

//     inline void reset()
//     {
//         start_ = std::chrono::steady_clock::now();
//         end_ = start_;
//     }

// private:
//     double &out_;
//     mutable Time start_;
//     mutable Time end_;
// };




/**
 * helper function for extracting atomic predicates occurring in a given
 * formula
 */
// void get_predicates(msat_env env, msat_term t, TermSet &out,
//                     bool include_bool_vars=false);


/**
 * returns the conjuction of all the elements for which the filter returns
 * true
 */
template <class Op, class C, class Filter>
msat_term make_reduce(msat_env env, Op op, const C &c, Filter f, msat_term base)
{
    msat_term res = base;
    for (auto it = c.begin(), end = c.end(); it != end; ++it) {
        msat_term t = *it;
        if (f(env, t)) {
            res = op(env, res, t);
            assert(!MSAT_ERROR_TERM(res));
        }
    }
    return res;
}


template <class C, class Filter>
msat_term make_and(msat_env env, const C &c, Filter f)
{
    return make_reduce(env, msat_make_and, c, f, msat_make_true(env));
}


template <class C>
msat_term make_and(msat_env env, const C &c)
{
    auto f = [](msat_env e, msat_term t) -> bool { return true; };
    return make_and(env, c, f);
}


template <class C>
msat_term make_or(msat_env env, const C &c)
{
    auto f = [](msat_env e, msat_term t) -> bool { return true; };
    return make_reduce(env, msat_make_or, c, f, msat_make_false(env));
}


inline msat_term make_impl(msat_env env, msat_term a, msat_term b)
{
    return msat_make_or(env, msat_make_not(env, a), b);
}


inline msat_term make_ite(msat_env env, msat_term c, msat_term t, msat_term e)
{
    return msat_make_and(env, make_impl(env, c, t),
                         make_impl(env, msat_make_not(env, c), e));
}
