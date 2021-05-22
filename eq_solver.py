#!/usr/bin/env python3


import math
from pprint import pprint
from itertools import combinations
from dataclasses import dataclass, field
from typing import Any


# Consider Factors also as terms
SUPER_TERMS = True


class SolveFailureError(Exception):
    pass


class InvalidTermError(Exception):
    pass


class TermTable:
    def __init__(self):
        self.table = {}
        self.locked_formulas = set()
        self.str_table = {}

    def add_formula(self, term, formula):
        term = str(term)
        str_formula = str(formula)
        if term not in self.table:
            self.table[term] = set()
            self.str_table[term] = set()
        if str_formula not in self.str_table[term]:
            self.table[term].add(formula)
            self.str_table[term].add(str_formula)

    def find_formulas(self, term):
        open_formulas = []
        if term not in self.table:
            raise InvalidTermError("Only The following can be solved for:\n"
                                    + "\n".join(list(self.table.keys())))
        for formula in self.table[term]:
            if formula not in self.locked_formulas:
                open_formulas.append(formula)
        return open_formulas

    def lock(self, formula):
        self.locked_formulas.add(formula)

    def unlock(self, formula):
        self.locked_formulas.remove(formula)


class Pow:
    def __init__(self, *args, expo=2):
        if len(args) != 1:
            raise ValueError("Invalid Number of Terms")
        self.arg = args[0]
        self.expo = expo

    def get_value(self, **kwterms):
        return pow(self.arg.get_value(**kwterms), self.expo)

    def get_terms(self):
        return self.arg.get_terms()

    def shift(self):
        return [Pow(*(self.arg,), expo=1/self.expo)]

    def __str__(self):
        return "pow({}, {})".format(self.arg, self.expo)

    def __repr__(self):
        return "<Pow {} Expo {}>".format(self.arg, self.expo)

    def sort_value(self):
        return str(self.arg)

    def __lt__(self, other):
        return self.sort_value() < other.sort_value()


@dataclass(frozen=True)
class Term:
    term: Any
    is_const: bool = False
    inverted: bool = False

    def invert(self):
        return Term(self.term, self.is_const, not self.inverted)

    def get_value(self, **kwargs):
        if self.is_const:
            value = self.term
        else:
            if self.term not in kwargs:
                value = solver.solve(self.term, **kwargs)
            else:
                value = kwargs[self.term]

        return 1/value if self.inverted else value

    def get_terms(self):
        if not self.is_const:
            return [self]
        return []

    def __repr__(self):
        return "<Term {}>".format(str(self))

    def __str__(self):
        if isinstance(self.term, float):
            str_term = "{:.2f}".format(self.term)
        else:
            str_term = str(self.term)
        if self.inverted:
            return "1/" + str_term
        return str_term

    def sort_value(self):
        return str(self.term)

    def __lt__(self, other):
        return self.sort_value() < other.sort_value()


class Factor:
    def __init__(self, *terms, negate=False):
        self.factors = sorted(list(terms))
        self.factors.sort()
        self.negate = negate

    def __str__(self):
        factor_str = "-" if self.negate else ""
        factor_str += "*".join(str(factor) for factor in self.factors)
        return factor_str.replace("--", "")

    def sort_value(self):
        return str(self.factors[0])

    def __lt__(self, other):
        return self.sort_value() < other.sort_value()

    def shift(self, factor=None):
        if factor is None:
            new_factors = []
            for i, factor in enumerate(self.factors):
                if isinstance(factor, Term):
                    new_factors.append(
                        Factor(factor.invert(), negate=self.negate))
                else:
                    new_factors.extend(factor.shift())
            return new_factors
        else:
            new_factor = []
            if isinstance(factor, Term):
                new_factor.append(
                    Factor(factor.invert(), negate=self.negate))
            else:
                new_factor.extend(factor.shift())
            return new_factor

    def get_value(self, **kwterms):
        return self.solve(**kwterms)

    def get_terms(self):
        terms = []
        for factor in self.factors:
            if isinstance(factor, Term) and not factor.is_const:
                terms.append(factor)
            else:
                terms.extend(factor.get_terms())
                if SUPER_TERMS:
                    for i in range(1, len(self.factors)+1):
                        for term_pair in combinations(self.factors, i):
                            terms.append(Factor(*term_pair))
        return terms

    def solve(self, **kwterms):
        try:
            prod = 1
            for factor in self.factors:
                factor_val = factor.get_value(**kwterms)
                prod *= factor_val

            if self.negate:
                prod *= -1
            return prod
        except SolveFailureError:
            if SUPER_TERMS:
                factor_val = solver.solve(str(self), **kwterms)
                
                if self.negate:
                    factor_val *= -1
                return factor_val
            else:
                raise

class Equation:
    def __init__(self, *factors):
        for factor in factors:
            if not isinstance(factor, Factor):
                raise ValueError("Equation Arguments must be Factors not '"
                                 + factor.__class__.__name__ + "'")
        factors = list(factors)
        if len(factors) > 1 and str(factors[0]) == "0":
            factors.pop(0)
                
        self.factors = factors

    def __str__(self):
        return "(" + "+".join(str(factor) for factor in self.factors) + ")"

    def shift(self, factor=None):
        if factor is None:
            new_factors = []
            for factor in self.factors:
                new_factors.append(
                    Factor(*factor.factors, negate=not factor.negate))

            return new_factors
        else:
            if factor not in self.factors:
                raise KeyError("Factor not in Equation")
            return Factor(*factor.factors, negate=not factor.negate)

    def get_terms(self):
        terms = []
        for factor in self.factors:
            terms.extend(factor.get_terms())
        return terms

    def get_value(self, **kwterms):
        return sum(factor.solve(**kwterms) for factor in self.factors)


class Formula:
    _lhs_str = ""
    _rhs_str = ""
    def __init__(self, lhs: Equation, rhs: Equation):
        if not isinstance(lhs, Equation):
            raise ValueError("LHS must be an Equation")
        if not isinstance(rhs, Equation):
            raise ValueError("RHS must be an Equation")
        self.lhs = lhs
        self.rhs = rhs
        self.terms = []
    
    @property
    def lhs_str(self):
        if not self._lhs_str:
            str(self)
        return self._lhs_str

    @property
    def rhs_str(self):
        if not self._rhs_str:
            str(self)
        return self._rhs_str

    def __str__(self):
        self._lhs_str = str(self.lhs)[1:-1]
        self._rhs_str = str(self.rhs)[1:-1]

        # REMOVE BUTIFICATIONS ON ERROR
        self._lhs_str = self._lhs_str.replace("+-", "-")
        self._rhs_str = self._rhs_str.replace("+-", "-")
        ##########3
        return self._lhs_str + "=" + self._rhs_str

    def get_terms(self):
        self.terms = self.lhs.get_terms() + self.rhs.get_terms()
        return self.terms

    def solve(self, solve_for, **kwterms):
        formula = self
        if self.lhs_str == solve_for:
            return formula.rhs.get_value(**kwterms)
        elif self.rhs_str == solve_for:
            return Formula(self.rhs, self.lhs).solve(solve_for, **kwterms)
        raise SolveFailureError


class Solver:
    def __init__(self):
        self.term_table = TermTable()

    def mul_permutate_formula(self, formula):
        rhs_factor = formula.rhs.factors[0]
        for sub_factor in rhs_factor.factors:
            shift_factor = [Factor(*(rhs_factor.shift(sub_factor)))]
            rhs_factors = []
            for factor in rhs_factor.factors:
                if factor != sub_factor:
                    if isinstance(factor, Factor):
                        rhs_factors.append(factor)
                        continue
                    rhs_factors.append(Factor(factor))
            if len(rhs_factors) == 0:
                rhs_factors = [FACTOR_ONE]
            lhs_factors = formula.lhs.factors
            if lhs_factors == [FACTOR_ONE]:
                lhs_factors = []
            formula_mul_shift = Formula(
                Equation(Factor(*(lhs_factors + shift_factor))),
                Equation(Factor(*rhs_factors))
            )

            self.add_formula(formula_mul_shift, super_call=False)
            self.permutate_formula(formula_mul_shift)

    def permutate_formula(self, formula):
        for factor in formula.rhs.factors:
            if factor == FACTOR_ZERO:
                continue
            shifted_factor = formula.rhs.shift(factor)
            
            rhs_factors = [f for f in formula.rhs.factors if f != factor]
            zeroed = False
            if len(rhs_factors) == 0:
                zeroed = True
                rhs_factors = [FACTOR_ZERO]

            formula_add_shift = Formula(
                Equation(*(formula.lhs.factors + [shifted_factor])),
                Equation(*rhs_factors)
            )

            self.add_formula(formula_add_shift, super_call=False)
            self.permutate_formula(formula_add_shift)
            
            if zeroed and str(factor) != str(FACTOR_ONE):
                self.mul_permutate_formula(formula)

    def right_shift_formula(self, formula):
        yield Formula(Equation(FACTOR_ZERO),
                      Equation(*(formula.rhs.factors + formula.lhs.shift())))

        yield Formula(Equation(FACTOR_ONE),
                      Equation(Factor(*(formula.rhs.factors
                                      + formula.lhs.factors[0].shift()))))

    def find_formula_permutations(self, formula):
        for formula in self.right_shift_formula(formula):
            self.add_formula(formula, super_call=False)
            self.permutate_formula(formula)

    def solve(self, req_term, **kwargs):
        
        formulas = self.term_table.find_formulas(req_term)
        soln = None
        for formula in formulas:
            self.term_table.lock(formula)
            try:
                soln = formula.solve(req_term, **kwargs)
            except (SolveFailureError, InvalidTermError):
                pass
            finally:
                self.term_table.unlock(formula)
        if soln is None:
            raise SolveFailureError("Unable To Solve Equation")
        return soln

    def add_formula(self, formula: Formula, super_call=True):
        if (super_call and (len(formula.lhs.factors) != 1
                or len(formula.lhs.factors[0].factors) != 1)):
            raise ValueError("Invalid Number of terms for formula")
        # for term in formula.get_terms():
        #     self.term_table.add_formula(term, formula)
        self.term_table.add_formula(formula.lhs_str, formula)
        self.term_table.add_formula(formula.rhs_str, formula)

        if super_call:
            self.find_formula_permutations(formula)

FACTOR_ZERO = Factor(Term(0, is_const=True))
FACTOR_ONE = Factor(Term(1, is_const=True))

# Vmax = a * omega
# F = ma = kx => m / k = x / a
# v = a * omega * cos( omega * t )
# find m / k
# find T = 2* pi * root(m/k)

PI_2 = 2 * math.pi

# omega = Vmax / a
formula_a = Formula(
    Equation(Factor(Term("omega"))),
    Equation(Factor(Term("Vmax"), Term("a", inverted=True))))

# f = omega / 2 * pi
formula_b = Formula(
    Equation(Factor(Term("f"))),
    Equation(Factor(Term("omega"), Term(PI_2, True, True))))

# m = x*k/a
formula_c = Formula(
    Equation(Factor(Term("m"))),
    Equation(Factor(Term("x"), Term("k"), Term("a", inverted=True))))

# T = 2*PI*root(m/k)
formula_d = Formula(
    Equation(Factor(Term("T"))), Equation(Factor(Term(PI_2, True),
    Pow(Factor(Term("m"), Term("k", inverted=True)), expo=.5))))

# T = 2*PI*root(l/g)
formula_e = Formula(
    Equation(Factor(Term("T"))), Equation(Factor(Term(PI_2, True),
    Pow(Factor(Term("l"), Term("g", inverted=True)), expo=.5))))

solver = Solver()
solver.add_formula(formula_a)
solver.add_formula(formula_b)
solver.add_formula(formula_c)
solver.add_formula(formula_d)
solver.add_formula(formula_e)

# print("TT")
# for k, v in solver.term_table.table.items():
#     for vs in v:
#         print("{:<40}: {}".format(k, str(vs)))

print(solver.solve("f", Vmax=62.8, a=.5))
print(solver.solve("T", a=15,x=3))
T = solver.solve("T", l=1.24, g=9.8)
print(T)
# print("EQS\n", "\n".join(list(map(str, solver.term_table.table["T"]))))
print(solver.solve("pow(1/g*l, 0.5)", l=1.24, g=9.8))

