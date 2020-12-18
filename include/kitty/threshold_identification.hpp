/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification

  \author CS-472 2020 Fall students
*/

#pragma once

#include <vector>
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include "traits.hpp"
#include "kitty.hpp"

namespace kitty {

    /**
     * Checks the unateness in truth table `tt` for variable `var_index`
     * @return true if function is unate in this variable, false if binate
     * Additionally, if function is *negative* unate for this variable, the var is added to the `flipped` set,
     * and the variable is flipped in the truth table
     */
    template<typename TT>
    bool check_unateness(TT &tt, uint8_t var_index, std::unordered_set<uint8_t> &flipped) {
        auto cof0 = cofactor0(tt, var_index);
        auto cof1 = cofactor1(tt, var_index);

        if (implies(cof0, cof1)) // positive unate
            return true;

        if (implies(cof1, cof0)) { // negative unate
            flipped.insert(var_index);
            flip_inplace(tt, var_index);
            return true;
        }

        return false;
    }

    /**
     * Initializes the ILP problem with (n+1) variables, naming and setting all columns to integer type
     * @return a pointer to the created ILP problem
     */
    template<typename TT>
    lprec *create_problem(TT &tt) {
        lprec *lp = make_lp(0, tt.num_vars() + 1); // the columns are w_1...w_n, and T

        // set w_i name and type
        for (uint8_t var = 1; var <= tt.num_vars(); var++) {
            set_int(lp, var, true);

            std::stringstream ss;
            ss << "w" << var;
            set_col_name(lp, var, ss.str().data());
        }

        // set T name and type
        set_int(lp, tt.num_vars() + 1, true);
        char name[] = "T";
        set_col_name(lp, tt.num_vars() + 1, name);

        return lp;
    }

    /**
     * Calculates whether given variable is active (has valuation 1) in given minterm
     * @return true if variable is active, false if inactive
     * Note: currently unused
     */
    bool is_var_in_minterm(uint8_t var_index, uint64_t minterm_index) {
        uint64_t frequency = 1ul << var_index;
        return (minterm_index / frequency) % 2 == 1;
    }

    /**
     * Adds a constraint to the ILP,
     * expressing the "threshold" relation for the valuation of variables given by `minterm_index`
     */
    template<typename TT>
    void add_minterm_constraint(TT &tt, uint64_t minterm_index, lprec *lp) {
        // Goal: represent the expression (\sum_{i=1}^n w_i x_i) - T
        std::vector<REAL> coefs = {0}; // index 0 is unused

        // Add all variables with a coef equal to x_i
        for (uint8_t var = 0; var < tt.num_vars(); var++) {
            uint64_t x_i = (minterm_index >> var) & 1ul;
            coefs.push_back(x_i);
        }
        // Add variable T with a coef of (-1)
        coefs.push_back(-1);

        if (get_bit(tt, minterm_index))             // function active for this minterm
            add_constraint(lp, coefs.data(), GE, 0);    // we want (\sum_{i=1}^n w_i x_i) - T >= 0
        else                                        // function inactive
            add_constraint(lp, coefs.data(), LE, -1);   // we want (\sum_{i=1}^n w_i x_i) - T <= -1
    }

    /**
     * Adds a constraint to the ILP for each variable to be positive
     */
    template<typename TT>
    void add_positive_contraint(TT &tt, lprec *lp) {
        for (uint8_t var = 0; var <= tt.num_vars(); var++) {
            std::vector<REAL> coef = {1};
            std::vector<int> col = {var + 1};
            add_constraintex(lp, 1, coef.data(), col.data(), GE, 0);
        }
    }

    /**
     * Sets the expression for the ILP's objective function
     */
    template<typename TT>
    void set_objective_fun(TT &tt, lprec *lp) {
        // Goal: represent the expression \sum_{i=1}^n w_i + T
        std::vector<REAL> coefs(tt.num_vars() + 2, 1.); // index 0 ignored; indexes 1..(n+1) equal to 1
        set_obj_fn(lp, coefs.data());
    }


    /*! \brief Threshold logic function identification

      Given a truth table, this function determines whether it is a threshold logic function (TF)
      and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

      f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

      where w_i are the weight values and T is the threshold value.
      The linear form of a TF is the vector [w_1, ..., w_n; T].

      \param tt The truth table
      \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
                 The linear form has `tt.num_vars()` weight values and the threshold value
                 in the end.
      \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
    */
    template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
    bool is_threshold(const TT &tt, std::vector<int64_t> *plf = nullptr) {
        std::vector<int64_t> linear_form;
        TT tt_copy = tt;
        const auto n = tt.num_vars();

        // Analyze function unateness (binate is not TF)
        std::unordered_set<uint8_t> flipped_vars;
        for (uint8_t i = 0; i < n; i++) {
            if (!check_unateness(tt_copy, i, flipped_vars))
                return false;
        }

        // Create LP problem
        lprec *lp = create_problem(tt_copy);

        // Add all constraints
        set_add_rowmode(lp, true);
        for (uint64_t minterm_idx = 0; minterm_idx < tt_copy.num_bits(); minterm_idx++) {
            add_minterm_constraint(tt_copy, minterm_idx, lp);
        }
        add_positive_contraint(tt_copy, lp);
        set_add_rowmode(lp, false);

        // Set objective function
        set_objective_fun(tt_copy, lp);

        // Set solver settings
        set_minim(lp);

        // Solve
        auto ret = solve(lp);

        // unsolvable ==> tt is non-TF
        if (ret != OPTIMAL) {
            delete_lp(lp);
            return false;
        }

        // if tt is TF
        // push the weight and threshold values into `linear_form`
        REAL *ptr_weights;
        get_ptr_variables(lp, &ptr_weights);

        int64_t T = 0;
        for (uint8_t var = 0; var < n; var++) {
            int64_t w_i = ptr_weights[var];
            // for flipped variables, flip back the weight & decrease RHS
            if (flipped_vars.count(var) > 0) {
                T -= w_i;
                linear_form.push_back(-w_i);
            } else {
                linear_form.push_back(w_i);
            }
        }
        T += ptr_weights[n];
        linear_form.push_back(T);

        if (plf) {
            *plf = linear_form;
        }
        delete_lp(lp);
        return true;
    }

} /* namespace kitty */
