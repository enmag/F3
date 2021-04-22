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

#include "utils.h"

// msat_config get_config(ModelGeneration model, bool interpolation, bool approx)
// {
//     msat_config cfg = msat_create_config();
//     if (MSAT_ERROR_CONFIG(cfg)) {
//         return cfg;
//     }

// #define OPT_(n,v) if (msat_set_option(cfg, n, v) != 0) goto err

//     // these are usually reasonable settings for the IC3 use case

//     // no random decisions in the SAT solver
//     OPT_("dpll.branching_random_frequency", "0");

//     // try not assigning values to theory atoms that occur only in
//     // already-satisfied clauses. Example: given a clause (P | (t >= 0)), if P
//     // is true, the value of (t >= 0) doesn't matter, and so it is a "ghost"
//     OPT_("dpll.ghost_filtering", "true");

//     // Handling disequalities might be potentially quite expensive (especially
//     // over the integers, where splitting of !(t = 0) into ((t < 0) | (t > 0))
//     // is needed), so we want to avoid this as much as possible. If (t = 0)
//     // occurs only positively in the input formula, but the SAT solver assigns
//     // it to false, we can avoid sending the literal !(t = 0) to the
//     // arithmetic solver, since if !(t = 0) causes an arithmetic conflict, we
//     // can always flip it (as the atom never occurs negated in the input
//     // formula, so assigning it to true can't cause any Boolean conflict)
//     OPT_("theory.la.pure_equality_filtering", "true");

//     // Turn off propagation of toplevel information. This is just overhead in
//     // an IC3 context (where the solver is called hundreds of thousands of
//     // times). Moreover, using it makes "lightweight" model generation (see
//     // below) not effective
//     OPT_("preprocessor.toplevel_propagation", "false");

//     // Avoid splitting negated equalities !(t = 0) if t is of rational
//     // type. Over the rationals, it is often cheaper to handle negated
//     // equalities in a special way rather than relying on the general
//     // splitting described above
//     OPT_("theory.la.split_rat_eq", "false");

//     // Do not reset the internal scores for variables in the SAT solver
//     // whenever a pop_backtrack_point() command is issued. In an IC3 context,
//     // the solver is called very often on very similar problems, so it makes
//     // sense to keep the variable scores computed so far, and maybe perform a
//     // full solver reset only every few thousand calls rather than
//     // reinitializing the scores at every pop()
//     OPT_("dpll.pop_btpoint_reset_var_order", "false");

//     // enable interpolation if required
//     OPT_("interpolation", interpolation ? "true" : "false");
//     OPT_("preprocessor.interpolation_ite_elimination", "true");

//     OPT_("theory.bv.bit_blast_mode", "1");
//     if (interpolation) {
//         // interpolation for BV requires the lazy solver
//         OPT_("theory.bv.bit_blast_mode", "0");
//         OPT_("theory.bv.eager", "false");
//     }

//     OPT_("model_generation", "false");
//     OPT_("bool_model_generation", "false");
//     switch (model) {
//     case NO_MODEL:
//         break;
//     case BOOL_MODEL:
//         // light-weight model generation, giving values only to atoms known to
//         // the SAT solver
//         OPT_("bool_model_generation", "true");
//         break;
//     case FULL_MODEL:
//         // full model generation, giving values to arbitrary terms
//         OPT_("model_generation", "true");
//         break;
//     }

//     if (approx) {
//         // turn off some expensive stuff when in approximate mode
//         OPT_("theory.la.laz_enabled", "false");
//         OPT_("theory.interface_eq_policy", "3");
//     }

//     return cfg;

//   err:
//     msat_destroy_config(cfg);
//     cfg.repr = NULL;
//     return cfg;
// }


// Logger Logger::the_logger_;


// void get_predicates(msat_env env, msat_term t, TermSet &out,
//                     bool include_bool_vars)
// {
//     struct Data {
//         TermSet &s;
//         bool include_bool_vars;

//         Data(TermSet &out, bool b): s(out), include_bool_vars(b) {}
//     };

//     auto visit = [](msat_env e, msat_term t, int preorder,
//                     void *data) -> msat_visit_status
//         {
//             Data *d = static_cast<Data *>(data);
//             TermSet &s = d->s;
//             if (preorder && msat_term_is_atom(e, t) &&
//                 (d->include_bool_vars ||
//                  !msat_term_is_boolean_constant(e, t))) {
//                 s.insert(t);
//                 return MSAT_VISIT_SKIP;
//             }
//             return MSAT_VISIT_PROCESS;
//         };
//     Data d(out, include_bool_vars);
//     msat_visit_term(env, t, visit, &d);
// }
