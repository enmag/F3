/** -*- C++ -*-
 *
 * Options
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

#include <string>

struct Options {
    // int verbosity;
    // bool witness;
    // bool nopreds;
    // std::string filename;
    // std::string trace;
    // int seed;
    // bool stack;
    // bool minpreds;
    // bool inc_ref;
    // bool generalize_pre;
    // bool solver_approx;
    // int solver_reset_interval;
    // int live_ref_maxiter;
    // bool live_ref_eager;
    // bool live_ref_ranking;
    // bool live_ref_templates;
    // bool live_no_cex;
    // bool live_bmc_cex;
    // bool live_klive_progress;
    // bool live_klive_only;
    // int live_klive_start;
    // bool live_klive_nondet;
    // bool live_klive_counter;
    // int prop_index;
    // bool bmc;
    // int bmc_max_k;
    bool check_witness;
    // std::string witness_check_script;
    bool ltl_single_fairness_sorted;

    Options()
    {
        // verbosity = 0;
        // witness = false;
        // nopreds = false;
        // generalize_pre = false;
        // solver_approx = false;
        // solver_reset_interval = 5000;
        // filename = "";
        // trace = "";
        // seed = 0;
        // stack = false;
        // minpreds = true;
        // inc_ref = false;
        // live_ref_maxiter = 10;
        // live_ref_eager = true;
        // live_ref_ranking = true;
        // live_ref_templates = true;
        // live_no_cex = true;
        // live_bmc_cex = true;
        // live_klive_progress = true;
        // live_klive_only = false;
        // live_klive_start = 0;
        // live_klive_nondet = false;
        // live_klive_counter = true;
        // prop_index = 0;
        // bmc = false;
        // bmc_max_k = -1;
        check_witness = false;
        // witness_check_script = "";
        ltl_single_fairness_sorted = true;
    }
};
