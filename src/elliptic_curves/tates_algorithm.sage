r"""An implementation of Tate's algorithm for Frey curves

This code allows for the computation of the possible conductors of an
elliptic curve which depends on some integral parameters.

EXAMPLES::

<Lots and lots of examples>

AUTHORS:

- Joey van Langen (2019-02-27): initial version

"""

# ****************************************************************************
#       Copyright (C) 2019 Joey van Langen <j.m.van.langen@outlook.com>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from sage.structure.sage_object import SageObject

from sage.schemes.elliptic_curves.kodaira_symbol import KodairaSymbol
from sage.schemes.elliptic_curves.kodaira_symbol import KodairaSymbol_class

from sage.all import Infinity

from sage.schemes.elliptic_curves.ell_generic import EllipticCurve_generic

def tates_algorithm(elliptic_curve, coefficient_ring=None, pAdics=None,
                    base_ring=None, prime=None, initial_values=None,
                    only_calculate=[], precision_cap=20, verbose=False):
    r"""Perform Tate's Algorithm on an elliptic curve dependent on
    parameters.

    We consider an elliptic curve $E$ defined by a Weierstrass
    equation of the form ..MATH::

        Y^2 + a_1 X Y + a_3 Y = X^3 + a_2 X^2 + a_4 X + a_6

    where $a_1, a_2, a_3, a_4, a_6$ are (multivariate) polynomials
    over some number field $L$ or a subring thereof. Considering the
    variables of these polynomials to take on undetermined values in
    the ring of integers of a subfield $K$ of $L$ we can see this as
    an elliptic curve over the field $L$.

    To determine the local behavior of $E$ at a finite prime $Q$ of
    $L$ we can follow Tate's algorithm, which in each step makes a
    decision based only on the roots of a polynomial in $a_1, a_2,
    a_3, a_4, a_6$ modulo some power of $Q$. Therefore each step only
    depends on the value of the variables modulo some finite power of
    the prime $P$ in $K$ below $Q$. Using p-adic trees and the
    function :func:`find_pAdic_roots` we can explicitly compute these
    values.

    .. NOTE::

    Even though each step in Tate's algorithm only depends on the
    value of the variables modulo some finite power of $P$ it is not
    guaranteed that the complete algorithm depends only on a finite
    power of $P$. In fact the termination of Tate's algorithm strongly
    depends on the fact that the discriminant of an elliptic curve is
    bounded to guarantee only finitely many steps in the
    algorithm. This might of course not be the case when the
    discriminant depends on variables.

    The code written here is not smart enough to detect the
    requirement for an infinite number of steps. The user is therefore
    advised to watch computations with this function closely, maybe
    even inspecting what is being done using the `verbose`
    argument. Especially the subalgorithm in step 7 for primes of
    characteristic 2 is very prone to getting stuck in an infinite
    number of steps, hence seeing step 7 appear very often when
    printing verbose is a good indication of a never ending
    computation.
    
    INPUT:
    
    - ``elliptic_curve`` -- The elliptic curve $E$
      
    - ``coefficient_ring`` -- The (multivariate) polynomial ring in
      which $a_1, a_2, a_3, a_4, a_6$ live. By default will be
      initialized as the base ring of $E$.
      
    - ``pAdics`` -- A pAdicBase object or None (default: None). This
      should give the p-adics on $L$ with respect to $Q$. If set to
      None, it will be initialized using the arguments `base_ring` and
      `prime`.
      
    - ``base_ring`` -- A ring or None (default: None). This should be
      a ring whose field of fractions is the field $L$. If set to None
      it will be initialized as the base ring of the argument
      `coefficient_ring`.
      
    - ``prime`` -- The prime $Q$ or None (default None). This may be
      given as a prime ideal or as a generator thereof if it is
      principal. If set to None it will be initialized using the
      p-adics given by the argument `pAdics`. It must be set if that
      argument is set to None.
      
    - ``initial_values`` -- A p-adic tree or None (default:
      None). This should be a tree containing the possible values for
      the variables in the argument `coefficient_ring`. It should be
      given as a pAdicTree that contains the same variables as
      `coefficient_ring`. If set to None, will be initialized as the
      full tree with these variables.
      
    - ``only_calculate`` -- (default: []) When set to a specific value
      or list of values, will ensure that the algorithm only
      calculates a certain quantity or quantities. Possible values are

        - 'conductor' -> Only calculate the conductor exponent

        - 'reduction_type' -> Only calculate the reduction type, i.e.
          good, split multiplicative, non-split multiplicative or
          additive, returned as None, 1, -1 or 0 respectively.

        - 'discriminant' -> Only calculate the valuation of the
          discriminant

        - 'type' -> Only calculate the Kodaira Symbol

        - 'minimal_model' -> Only calculate the minimal model for this
          elliptic curve

      By default the function computes all these quantities, but in
      this way they can be selection. The function will skip over all
      computations that are not required to determine those quantities
      so this might save time.

    - ``precision_cap`` -- A non-negative integer (default: 20). This
      argument determines the highest precision that will be used for
      the values of the variables of `coefficient_ring`. Note that
      setting this too low might result in inaccurate results, for
      which a warning will appear if this is the case. Setting this
      argument too high might result in endless and slow computations.
    
    - ``verbose`` -- A boolean value or an integer (default: False).
      When set to True or any value larger then zero will print
      comments to stdout about the computations being done whilst
      busy. If set to False or 0 will not print such comments. If set
      to any negative value will also prevent the printing of any
      warnings. Will print more message if set to a higher value.
    
    OUTPUT:
    
    The output will be a FreyCurveLocalData object containing the
    local data of the elliptic curve $E$ for the prime $Q$. If the
    argument `only_calculate` was not the empty list will instead
    return a list consisting of the requested values to be computed in
    the order they were requested in in `only_calculate`.

    If the output depends on the specific values of the variables,
    will return a ConditionalValue with for each case the value as
    mentioned above and the condition that should hold on the
    variables for this value to be attained.
    
    EXAMPLES:
    
    To be made

    """
    _check_elliptic_curve(elliptic_curve)
    coefficient_ring = _init_coefficient_ring(coefficient_ring,
                                               elliptic_curve)
    pAdics = _init_pAdics(pAdics, base_ring, prime, coefficient_ring)
    S = _init_polynomial_ring(coefficient_ring, pAdics)
    variables = _init_variables_tate(S)
    T = _init_initial_values(initial_values, pAdics, variables)
    newCases, doneCases = _init_cases(T, elliptic_curve)
    only_calculate = _init_str_list(only_calculate)
    
    #The main loop performing the different steps.
    while len(newCases) > 0:
        cases = newCases
        newCases = []
        for case in cases:
            if case.has_key('next_step'):
                if case['next_step'] == 1:
                    if verbose > 0:
                        print "Performing step 1"
                    _tate_step1(case['E'], S, pAdics, case['T'], case['E0'],
                                variables=variables, result=newCases,
                                verbose=(verbose-1 if verbose>0 else verbose),
                                precision_cap=precision_cap)
                elif case['next_step'] == 2:         
                    if verbose > 0:
                        print "Performing the transformation for step 2"  
                    _tate_step2_t(case['E'], S, pAdics, case['T'], case['E0'],
                                  variables=variables, result=newCases,
                                  verbose=(verbose-1 if verbose>0 else verbose),
                                  precision_cap=precision_cap)
                elif case['next_step'] == 2 + 1/2:
                    if verbose > 0:
                        print "Performing step 2"
                    _tate_step2(case['E'], S, pAdics, case['T'], case['E0'],
                                variables=variables, result=newCases,
                                verbose=(verbose-1 if verbose>0 else verbose),
                                precision_cap=precision_cap)
                elif case['next_step'] == 3:
                    if verbose > 0:
                        print "Performing step 3"
                    _tate_step3(case['E'], S, pAdics, case['T'], case['E0'],
                                variables=variables, result=newCases,
                                verbose=(verbose-1 if verbose>0 else verbose),
                                precision_cap=precision_cap)
                elif case['next_step'] == 4:
                    if verbose > 0:
                        print "Performing step 4"
                    _tate_step4(case['E'], S, pAdics, case['T'], case['E0'],
                                variables=variables, result=newCases,
                                verbose=(verbose-1 if verbose>0 else verbose),
                                precision_cap=precision_cap)
                elif case['next_step'] == 5:
                    if verbose > 0:
                        print "Performing step 5"
                    _tate_step5(case['E'], S, pAdics, case['T'], case['E0'],
                                variables=variables, result=newCases,
                                verbose=(verbose-1 if verbose>0 else verbose),
                                precision_cap=precision_cap)
                elif case['next_step'] == 6:
                    if verbose > 0:
                        print "Performing the transformation for step 6"
                    _tate_step6_t(case['E'], S, pAdics, case['T'], case['E0'],
                                  variables=variables, result=newCases,
                                  verbose=(verbose-1 if verbose>0 else verbose),
                                  precision_cap=precision_cap)
                elif case['next_step'] == 6 + 1/2:
                    if verbose > 0:
                        print "Performing step 6"
                    _tate_step6(case['E'], S, pAdics, case['T'], case['E0'],
                                variables=variables, result=newCases,
                                verbose=(verbose-1 if verbose>0 else verbose),
                                precision_cap=precision_cap)
                elif case['next_step'] == 7:
                    if verbose > 0:
                        print "Performing step 7"
                    _tate_step7(case['E'], S, pAdics, case['T'], case['E0'],
                                case, only_calculate, variables=variables,
                                result=newCases,
                                verbose=(verbose-1 if verbose>0 else verbose),
                                precision_cap=precision_cap)
                elif case['next_step'] in QQ and case['next_step'] < 8:
                    n , b = _decode_quotient( case['next_step'] - 7 )
                    if b == 0:
                        if verbose > 0:
                            print "Performing the transformation for step 7sub"
                        _tate_step7sub_t(case['E'], S, pAdics, case['T'],
                                         case['E0'], n, variables=variables,
                                         result=newCases,
                                         verbose=(verbose-1 if verbose>0
                                                  else verbose),
                                         precision_cap=precision_cap)
                    else:
                        if verbose > 0:
                            print "Performing step 7sub"
                        _tate_step7sub(case['E'], S, pAdics, case['T'],
                                       case['E0'], n, variables=variables,
                                       result=newCases,
                                       verbose=(verbose-1 if verbose>0
                                                else verbose),
                                       precision_cap=precision_cap)
                elif case['next_step'] == 8:
                    if verbose > 0:
                        print "Performing the transformation for step 8"
                    _tate_step8_t(case['E'], S, pAdics, case['T'], case['E0'],
                                  variables=variables, result=newCases,
                                  verbose=(verbose-1 if verbose>0 else verbose),
                                  precision_cap=precision_cap)
                elif case['next_step'] == 8 + 1/2:
                    if verbose > 0:
                        print "Performing step 8"
                    _tate_step8(case['E'], S, pAdics, case['T'], case['E0'],
                                variables=variables, result=newCases,
                                verbose=(verbose-1 if verbose>0 else verbose),
                                precision_cap=precision_cap)
                elif case['next_step'] == 9:
                    if verbose > 0:
                        print "Performing the transformation for step 9"
                    _tate_step9_t(case['E'], S, pAdics, case['T'], case['E0'],
                                  variables=variables, result=newCases,
                                  verbose=(verbose-1 if verbose>0 else verbose),
                                  precision_cap=precision_cap)
                elif case['next_step'] == 9 + 1/2:
                    if verbose > 0:
                        print "Performing step 9"
                    _tate_step9(case['E'], S, pAdics, case['T'], case['E0'],
                                variables=variables, result=newCases,
                                verbose=(verbose-1 if verbose>0 else verbose),
                                precision_cap=precision_cap)
                elif case['next_step'] == 10:
                    if verbose > 0:
                        print "Performing step 10"
                    _tate_step10(case['E'], S, pAdics, case['T'], case['E0'],
                                 variables=variables, result=newCases,
                                 verbose=(verbose-1 if verbose>0 else verbose),
                                 precision_cap=precision_cap)
                elif case['next_step'] == 11:
                    if verbose > 0:
                        print "Performing step 11"
                    _tate_step11(case['E'], S, pAdics, case['T'], case['E0'],
                                 variables=variables, result=newCases,
                                 verbose=(verbose-1 if verbose>0 else verbose),
                                 precision_cap=precision_cap)
                else:
                    print "Unknown step number %s requested"%case['next_step']
            elif _should_calculate_vDelta(case, only_calculate):
                _tate_calculate_vDelta(case['E'], S, pAdics, case['T'], case,
                                       variables=variables, result=newCases,
                                       verbose=verbose,
                                       precision_cap=precision_cap)
            elif _should_calculate_m(case, only_calculate):
                _tate_calculate_m(case['E'], S, pAdics, case['T'], case,
                                  variables=variables, result=newCases,
                                  verbose=verbose, precision_cap=precision_cap)
            elif _should_calculate_f(case, only_calculate):
                _tate_calculate_f(case['E'], S, pAdics, case['T'], case,
                                  variables=variables, result=newCases,
                                  verbose=verbose, precision_cap=precision_cap)
            elif _should_calculate_n(case, only_calculate):
                _tate_calculate_n(case['E'], S, pAdics, case['T'], case,
                                  variables=variables, result=newCases,
                                  verbose=verbose, precision_cap=precision_cap)
            elif _should_calculate_split(case, only_calculate):
                _tate_calculate_split(case['E'], S, pAdics, case['T'], case,
                                      variables=variables, result=newCases,
                                      verbose=verbose,
                                      precision_cap=precision_cap)
            elif _should_calculate_c(case, only_calculate):
                _tate_calculate_c(case['E'], S, pAdics, case['T'], case,
                                  variables=variables, result=newCases,
                                  verbose=verbose,precision_cap=precision_cap)
            else:
                _tate_finish(case, only_calculate, result=doneCases,
                             verbose=verbose, variables=variables)
        
    return _tate_cleanup(doneCases)

def _least_power(poly_list, pAdics):
    r"""Get the smallest valuation among coefficients of polynomials

    INPUT:

    - ``poly_list`` -- A list of polynomials

    - ``pAdics`` -- The p-adics to be used for the valuation

    OUTPUT:

    The smallest valuation among the coefficients of the given
    polynomials, or Infinity if there were no non-zero polynomials.

    """
    result = Infinity
    for poly in poly_list:
        result = min([result]+[pAdics.valuation(c)
                               for c in poly.coefficients()])
    return result

def _determine_level(poly_list, pAdics, T, max_value):
    r"""Determine the level of nodes sufficient for polynomials to have a
    fixed value modulo some prime power.

    Let $L / K$ be an extension of number fields and $Q$ be a finite
    prime of $L$ lying above the prime $P$ of $K$. For a list of
    (multivariate) polynomials $f_1, \ldots, f_n$ over $L$ one can
    wonder up to what power $r$ of the prime $P$ we have to determine
    the value of the variables in the ring of integers of $K$ to fix
    the value of all polynomials modulo $Q^s$. Given $s$ this function
    computes $r$.

    INPUT:

    - ``poly_list`` -- The list of polynomials $f_1, \ldots, f_n$
    
    - ``pAdics`` -- The p-adics determined by $L$ and $Q$

    - ``T`` -- The root of the p-adic tree containing the possible
      values for the variables

    - ``max_value`` -- The integer $s$

    OUTPUT:

    The smallest possible integer $r$ or $0$ if it does not exist or
    is smaller than $0$.

    """
    level = max_value - _least_power(poly_list, pAdics)
    if level > -Infinity:
        level = ceil(level/pAdics.extension_multiplicity(T.pAdics()))
    if level < 0:
        level = 0
    return level

def _get_cases_invariant(poly, pAdics, T, name, general_case, variables=None,
                        verbose=False, precision=20, result=[],
                        precision_cap=20, **kwds):
    r"""Determine the different valuations a polynomial can have.

    INPUT:

    - ``poly`` -- A (multivariate) polynomial

    - ``pAdics`` -- The p-adics to be used

    - ``T`` -- The root of the p-adic tree containing the possible
      values for the variables

    - ``name`` -- A string which is the name to be assigned to the
      valuation of the polynomial

    - ``general_case`` -- A dictionary that is a template for the
      cases to be returned.

    - ``variables`` -- A list of the variables of the polynomial or
      None (default) for it to be initialized from the polynomial.

    - ``verbose`` -- Verbosity argument

    - ``precision`` -- The precision to be used when computing the
      valuation

    - ``precision_cap`` -- The largest precision to be used on the
      variables

    - ``result`` -- A list (default: []) containing resulting cases to
      which the different cases of this computations should be
      appended

    OUPUT:

    The given list `result` appended with copies of the given
    `general_case`. For each copy there was added an entry with as key
    the given name and as value a possible valuation of the
    polynomial; and an entry with as key 'T' and as value the root of
    a p-adic tree containing those values in the given p-adic tree for
    which the corresponding valuation of the polynomial is attained.

    """
    Tlist, v_min = find_pAdic_roots(poly, pAdics=pAdics, variables=variables,
                                    value_tree=T, precision=precision,
                                    verbose=verbose, give_list=True,
                                    precision_cap=precision_cap)
    for i in range(len(Tlist)):
        if not Tlist[i].is_empty():
            case = general_case.copy()
            case[name] = v_min + i
            case['T'] = Tlist[i]
            result.append(case)
    return result

def _get_two_cases_invariant(poly, pAdics, T, bndry, case_big, case_small,
                             variables=None, verbose=False, result=[],
                             precision_cap=20, **kwds):
    r"""Distinguish whether a polynomial has at least a certain valuation
    or not

    INPUT:

    - ``poly`` -- The polynomial

    - ``pAdics`` -- The p-adics to be used

    - ``T`` -- The root of a p-adic tree containing the possible
      values for the variables

    - ``bndry`` -- An integer giving the valuation at which we
      distinguish

    - ``case_big`` -- A dictionary that is a template for the case the
      valuation is at least `bndry`

    - ``case_small`` -- A dictionary that is a template for the case
      the valuation is less then `bndry`

    - ``variables`` -- A list of the variables of the polynomial or
      None if it should be determined from the polynomial
    
    - ``verbose`` -- Verbosity argument

    - ``result`` -- A list of resulting cases to which the cases
      determined by this function should be added.

    - ``precision_cap`` -- A cap on the precision used for the
      variables

    OUTPUT:

    The given list `result` with some cases added.

    In case there is possible values for the variables in which the
    valuation of the polynomial is at least `bndry` then the case
    `case_big` was added with an added entry with key `T` and value
    the root of a p-adic tree containing all those values for which
    this is the case.

    If there is possible values for the variables in which the
    valuation of the polynomial is less then `bndry` then the case
    `case_small` was added with and added entry with key `T` and value
    the root of a p-adic tree containing all those values for which
    this is the case.

    """
    Tbig, Tsmall = find_pAdic_roots(poly, pAdics=pAdics, variables=variables,
                                    value_tree=T, precision=bndry,
                                    verbose=verbose,
                                    precision_cap=precision_cap)
    if not Tbig.is_empty():
        case_big['T'] = Tbig
        result.append(case_big)
    if not Tsmall.is_empty():
        case_small['T'] = Tsmall
        result.append(case_small)
    return result
        
def _get_number_of_roots_cases(poly_list, pAdics, T, name, general_case,
                              variables=None, verbose=False, result=[],
                              **kwds):
    r"""Determines the possible roots a polynomial with as coefficients
    multivariate polynomials can have.

    Let $L / K$ be an extension of number fields and let $Q$ be a
    finite prime of $L$ above the prime $P$ of $K$. For (multivariate)
    polynomials $f_0, \ldots, f_n$ over $L$ we can construct the
    polynomial .. MATH::
    
        F(X) = f_0*X^n + ... + f_{n-1}*X + f_n

    If the variables of the polynomials $f_0, \ldots, f_n$ take on
    values in the ring of integers of $K$ such that the valuations of
    $f_0, \ldots, f_n$ are non-negative, the above defines a
    polynomial over the residue field of $Q$. This function determines
    how many roots this polynomial has over that residue field and for
    which value that number of roots occurs.

    INPUT:

    - ``poly_list`` -- A list of the polynomials $f_0, \ldots, f_n$ in
      that order

    - ``pAdics`` -- The p-adics defined by $L$ and $Q$

    - ``T`` -- The root of a p-adic tree giving the possible values
      for the variables. These should be such that the valuation of
      $f_0, \ldots, f_n$ should be non-negative.
    
    - ``name`` -- A string that is the name that should be assigned to
      the number of roots of the polynomial $F$

    - ``general_case`` -- A dictionary that is a template for the
      cases to be returned

    - ``variables`` -- A list of the variables of the polynomials or
      None if it should be determined from the polynomials

    - ``verbose`` -- Verbosity argument

    - ``result`` -- A list of resulting cases to which the results of
      this function should be appended

    OUTPUT:

    The list of cases `result` with some cases appended. For each
    possible number of roots of the polynomial $F$ over the residue
    field of $Q$ a copy of the case `general_case` is appended with as
    additional entries:

    - An entry with as key the string given by `name` and as value a
      number of roots the polynomial $F$ has over the residue field of
      $Q$.

    - An entry with as key 'T' and as value the root of a p-adic tree
      containing all those values for the variables in the given tree
      for which this number of roots for $F$ is attained.

    """
    Tdict = {}
    n = _determine_level(poly_list, pAdics, T, 1)
    F = pAdics.residue_field()
    S.<x> = F[]
    child_list = T.children_at_level(n)
    if verbose > 0:
        print "Checking irreducibility in %d cases"%len(child_list)
    for child in child_list:
        coeff_list = [F(poly(child.representative())) for poly in poly_list]
        f = 0
        k = len(coeff_list)-1
        for i in range(k+1):
            f += coeff_list[i] * x^(k-i)
        m = sum([r[1] for r in f.roots()])
        if not Tdict.has_key(m):
            Tdict[m] = pAdicNode(pAdics=T.pAdics(), width=T.width)
        Tdict[m].merge(child, from_root=True)
    for (m,Tm) in Tdict.iteritems():
        case = general_case.copy()
        case[name] = m
        case['T'] = Tm
        result.append(case)
    return result
    
def _tate_step1(E, S, pAdics, T, E0, **kwds):
    r"""Perform step 1 of Tate's algorithm.

    Stop if the valuation of the discriminant of the elliptic curve is
    less than 1. Continue to step 2 otherwise.

    In case we stop we have:
    
    - Kodaira symbol: $I_0$

    - valuation of the minimal discriminant: 0
    
    - number of components: 1

    - exponent of the conductor: 0

    - order of the group of components: 1

    INPUT:

    - ``E`` -- The elliptic curve to work on

    - ``S`` -- The polynomial ring over which the coefficients of `E`
      should live

    - ``pAdics`` -- The p-adics to be used

    - ``T`` -- The root of a p-adic tree containing the possible value
      of the variables of `S`

    - ``E0`` -- The current candidate of a minimal model for `E`

    - ``variables`` -- A list of the variables of the polynomial or
      None if it should be determined from `S`
    
    - ``verbose`` -- Verbosity argument

    - ``result`` -- A list of resulting cases to which the cases
      determined by this function should be added.

    - ``precision_cap`` -- A cap on the precision used for the
      variables

    OUTPUT:

    The list given by `result` with some added cases. Added cases
    could include the case in which we stop at step 1 and the case we
    continue onto step 2, but only if some value of the variables
    would give such a case.

    """
    case_big = dict(E=E, next_step=2, E0=E0)
    case_small = dict(E=E, vDelta=0, m=1, f=0, c=1, KS="I0", E0=E0) 
    return _get_two_cases_invariant(S(E.discriminant()), pAdics, T, 1,
                                    case_big, case_small, **kwds)
    
def _tate_step2_t(E, S, pAdics, T, E0, verbose=False, result=[], **kwds):
    r"""Perform the transformation necessary before step 2 of Tate's
    algorithm.

    Move the singular point to (0,0), i.e. transform the curve such
    that it has a Weierstrass equation of the form .. MATH::

        Y^2 + a_1 X Y + a_3 Y = X^3 + a_2 X^2 + a_4 X + a_6

    for which $a_3$, $a_4$ and $a_6$ have valuation at least 1.

    INPUT:

    - ``E`` -- The elliptic curve to work on

    - ``S`` -- The polynomial ring over which the coefficients of `E`
      should live

    - ``pAdics`` -- The p-adics to be used

    - ``T`` -- The root of a p-adic tree containing the possible value
      of the variables of `S`

    - ``E0`` -- The current candidate of a minimal model for `E`

    - ``variables`` -- A list of the variables of the polynomial or
      None if it should be determined from `S`
    
    - ``verbose`` -- Verbosity argument

    - ``result`` -- A list of resulting cases to which the cases
      determined by this function should be added.

    - ``precision_cap`` -- A cap on the precision used for the
      variables

    OUTPUT:

    The list given by `result` with some added cases. Added cases
    include the possible transformations to put the elliptic curve in
    the described form with the appropiate values for the variables
    for this to be the case.

    """
    R = pAdics.order()
    P = pAdics.prime_ideal()
    F = pAdics.residue_field()
    char = pAdics.characteristic()
    replaceCases = dict()
    
    # The parameter s is used to compute
    # - square roots in characteristic 2
    # - cube roots in characteristic 3
    # In both cases these roots are unique and can be computed
    # by taking an element to the power s
    s = 0
    if char == 2:
        if R == ZZ and P in ZZ.ideal_monoid():
            s = ((ZZ.quotient(P.gen() - 1)(2))^(-1)).lift()
        else:
            s = ((ZZ.quotient(ZZ(norm(P) - 1))(2))^(-1)).lift()
    if char == 3:
        if R == ZZ and P in ZZ.ideal_monoid():
            s = ((ZZ.quotient(P.gen() - 1)(3))^(-1)).lift() 
        else:
            s = ((ZZ.quotient(ZZ(norm(P) - 1))(3))^(-1)).lift()
    if s == 0:
        s = 1

    # Determining the necessary transformations
    level = _determine_level([S(E.a1()), S(E.a2()), S(E.a3()), S(E.a4()),
                              S(E.a6())], pAdics, T, 1)
    if verbose > 0:
        print ("Determining singular point for " +
               str(T.count_children_at_level(level)) + " cases")
    for node in T.children_at_level(level):
        # Determining the singular point x,y
        a1 = F(S(E.a1())(node.representative()))
        a2 = F(S(E.a2())(node.representative()))
        a3 = F(S(E.a3())(node.representative()))
        a4 = F(S(E.a4())(node.representative()))
        a6 = F(S(E.a6())(node.representative()))    
        if char == 2:
            if a1 == 0:
                x = a4^s
                y = (a6 + a2*a4)^s
            else:
                x = a3 / a1
                y = (x^2 + a4) / a1
        else:
            # Coordinate transformation to end up in the case
            # where a1 = a3 = 0, hence y = 0
            a22 = a2 + a1^2 / 4
            a42 = a4 + a1*a3 / 2
            a62 = a6 + a3^2 / 4
            y = 0
            if char == 3:
                if a22 == 0:
                    x = (-a62)^s
                else:
                    x = -a42 / a22
            else:
                # Coordinate transformation to end up in the case where
                # also a2 = 0
                a43 = a42 - a22^2 / 3
                a63 = a62 - a22*a42 / 3 + 2*a22^3 / 27                
                if a43 == 0:
                    x = 0
                else:
                    x = -3*a63 / (2*a43)                
                # Transforming back
                x = x - a22 / 3                
            # Transforming back
            y = y - a1*x / 2 - a3 / 2
        singularPoint = tuple([x,y])
        if singularPoint in replaceCases:
            replaceCases[singularPoint].merge(node, from_root=True)
        else:
            Tn = pAdicNode(pAdics=T.pAdics(), width=T.width)
            Tn.merge(node, from_root=True)
            replaceCases[singularPoint] = Tn

    # Doing the actual transformations
    if verbose > 0:
        print "Performing transformation for %d cases"%(len(replaceCases),)
    for (point,Tn) in replaceCases.iteritems():
        xn = F.lift(point[0])
        yn = F.lift(point[1])
        En = E.rst_transform(xn,0,yn)
        result.append(dict(next_step=2+1/2, T=Tn, E=En, E0=E0))            
    return result
    
def _tate_step2(E, S, pAdics, T, E0, **kwds):
    r"""Perform step 2 of Tate's algorithm.

    Stop if the valuation of the invariant $b_2$ of the elliptic curve
    is less than 1. Continue to step 3 otherwise.

    In case we stop we have:
    
    - Kodaira symbol: $I_n$

    INPUT:

    - ``E`` -- The elliptic curve to work on

    - ``S`` -- The polynomial ring over which the coefficients of `E`
      should live

    - ``pAdics`` -- The p-adics to be used

    - ``T`` -- The root of a p-adic tree containing the possible value
      of the variables of `S`

    - ``E0`` -- The current candidate of a minimal model for `E`

    - ``variables`` -- A list of the variables of the polynomial or
      None if it should be determined from `S`
    
    - ``verbose`` -- Verbosity argument

    - ``result`` -- A list of resulting cases to which the cases
      determined by this function should be added.

    - ``precision_cap`` -- A cap on the precision used for the
      variables

    OUTPUT:

    The list given by `result` with some added cases. Added cases
    could include the case in which we stop at step 2 and the case we
    continue onto step 3, but only if some value of the variables
    would give such a case.

    """
    case_big = dict(E=E, next_step=3, E0=E0)
    case_small = dict(E=E, f=1, KS="In", E0=E0) 
    return _get_two_cases_invariant(S(E.b2()), pAdics, T, 1, case_big,
                                    case_small, **kwds)

def _tate_step3(E, S, pAdics, T, E0, **kwds):
    r"""Perform step 3 of Tate's algorithm.

    Stop if the valuation of the invariant $a_6$ of the elliptic curve
    is less than 2. Continue to step 4 otherwise.

    In case we stop we have:
    
    - Kodaira symbol: $II$
    
    - number of components: 1

    - order of the group of components: 1

    INPUT:

    - ``E`` -- The elliptic curve to work on

    - ``S`` -- The polynomial ring over which the coefficients of `E`
      should live

    - ``pAdics`` -- The p-adics to be used

    - ``T`` -- The root of a p-adic tree containing the possible value
      of the variables of `S`

    - ``E0`` -- The current candidate of a minimal model for `E`

    - ``variables`` -- A list of the variables of the polynomial or
      None if it should be determined from `S`
    
    - ``verbose`` -- Verbosity argument

    - ``result`` -- A list of resulting cases to which the cases
      determined by this function should be added.

    - ``precision_cap`` -- A cap on the precision used for the
      variables

    OUTPUT:

    The list given by `result` with some added cases. Added cases
    could include the case in which we stop at step 3 and the case we
    continue onto step 4, but only if some value of the variables
    would give such a case.

    """
    case_big = dict(E=E, next_step=4, E0=E0)
    case_small = dict(E=E, KS="II", m=1, c=1, E0=E0)
    char = pAdics.characteristic()
    if char != 2 and char != 3:
        case_small['vDelta'] = 2
        case_small['f'] = 2
    return _get_two_cases_invariant(S(E.a6()), pAdics, T, 2, case_big,
                                    case_small, **kwds)
    
def _tate_step4(E, S, pAdics, T, E0, **kwds):
    r"""Perform step 4 of Tate's algorithm.

    Stop if the valuation of the invariant $b_8$ of the elliptic curve
    is less than 3. Continue to step 5 otherwise.

    In case we stop we have:
    
    - Kodaira symbol: $III$,
    
    - number of components: 2

    - order of the group of components: 2

    INPUT:

    - ``E`` -- The elliptic curve to work on

    - ``S`` -- The polynomial ring over which the coefficients of `E`
      should live

    - ``pAdics`` -- The p-adics to be used

    - ``T`` -- The root of a p-adic tree containing the possible value
      of the variables of `S`

    - ``E0`` -- The current candidate of a minimal model for `E`

    - ``variables`` -- A list of the variables of the polynomial or
      None if it should be determined from `S`
    
    - ``verbose`` -- Verbosity argument

    - ``result`` -- A list of resulting cases to which the cases
      determined by this function should be added.

    - ``precision_cap`` -- A cap on the precision used for the
      variables

    OUTPUT:

    The list given by `result` with some added cases. Added cases
    could include the case in which we stop at step 4 and the case we
    continue onto step 5, but only if some value of the variables
    would give such a case.

    """
    case_big = dict(E=E, next_step=5, E0=E0)
    case_small = dict(E=E, KS="III", m=2, c=2, E0=E0)
    char = pAdics.characteristic()
    if char != 2:
        case_small['vDelta'] = 3
        case_small['f'] = 2
    return _get_two_cases_invariant(S(E.b8()), pAdics, T, 3, case_big,
                                    case_small, **kwds)

def _tate_step5(E, S, pAdics, T, E0, **kwds):
    r"""Perform step 5 of Tate's algorithm.

    Stop if the valuation of the invariant $b_6$ of the elliptic curve
    is less than 3. Continue to step 6 otherwise.

    In case we stop we have:
    
    - Kodaira symbol: $IV$
    
    - number of components: 3

    INPUT:

    - ``E`` -- The elliptic curve to work on

    - ``S`` -- The polynomial ring over which the coefficients of `E`
      should live

    - ``pAdics`` -- The p-adics to be used

    - ``T`` -- The root of a p-adic tree containing the possible value
      of the variables of `S`

    - ``E0`` -- The current candidate of a minimal model for `E`

    - ``variables`` -- A list of the variables of the polynomial or
      None if it should be determined from `S`
    
    - ``verbose`` -- Verbosity argument

    - ``result`` -- A list of resulting cases to which the cases
      determined by this function should be added.

    - ``precision_cap`` -- A cap on the precision used for the
      variables

    OUTPUT:

    The list given by `result` with some added cases. Added cases
    could include the case in which we stop at step 5 and the case we
    continue onto step 6, but only if some value of the variables
    would give such a case.

    """
    case_big = dict(E=E, next_step=6, E0=E0)
    case_small = dict(E=E, KS="IV", m=3, E0=E0)
    char = pAdics.characteristic()
    if char != 3:
        case_small['vDelta'] = 4
        case_small['f'] = 2
    return _get_two_cases_invariant(S(E.b6()), pAdics, T, 3,
                                   case_big, case_small, **kwds)

def _tate_step6_t(E, S, pAdics, T, E0, verbose=False, result=[], **kwds):
    r"""Perform the transformation necessary before step 6 of Tate's
    algorithm.

    Transform the curve such that it has a Weierstrass equation of the
    form .. MATH::

        Y^2 + a_1 X Y + a_3 Y = X^3 + a_2 X^2 + a_4 X + a_6

    for which $a_1$ and $a_2$ having valuation at least 1, $a_3$ and
    $a_4$ having valuation at least 2 and $a_6$ having valuation at
    least 3

    INPUT:

    - ``E`` -- The elliptic curve to work on

    - ``S`` -- The polynomial ring over which the coefficients of `E`
      should live

    - ``pAdics`` -- The p-adics to be used

    - ``T`` -- The root of a p-adic tree containing the possible value
      of the variables of `S`

    - ``E0`` -- The current candidate of a minimal model for `E`

    - ``variables`` -- A list of the variables of the polynomial or
      None if it should be determined from `S`
    
    - ``verbose`` -- Verbosity argument

    - ``result`` -- A list of resulting cases to which the cases
      determined by this function should be added.

    - ``precision_cap`` -- A cap on the precision used for the
      variables

    OUTPUT:

    The list given by `result` with some added cases. Added cases
    include the possible transformations to put the elliptic curve in
    the described form with the appropiate values for the variables
    for this to be the case.

    """
    pi = pAdics.uniformizer()
    char = pAdics.characteristic()
    R = pAdics.order()
    P = pAdics.prime_ideal()
    F = pAdics.residue_field()

    # Determining the diferent transformations needed
    changeDict = dict()   
    if char != 2:
        a1 = S(E.a1())
        a31 = S(E.a3()/pi)     
        half = (F(2)^(-1))
        level = _determine_level([a1, a31], pAdics, T, 1)
        if verbose > 0:
            print ("Determining necessary transformation for " +
                   str(T.count_children_at_level(level)) + " cases")
        for node in T.children_at_level(level):
            alpha = -half * F(a1(node.representative()))
            a31_ev = F(a31(node.representative()))
            beta = -half * a31_ev
            alphaBetaPair = tuple([alpha, beta])
            if alphaBetaPair in changeDict:
                changeDict[alphaBetaPair].merge(node, from_root=True)
            else:
                T0 = pAdicNode(pAdics=T.pAdics(), width=T.width)
                T0.merge(node, from_root=True)
                changeDict[alphaBetaPair] = T0
    else:
        if R == ZZ and P in ZZ.ideal_monoid():
            sqrtPower = ((ZZ.quotient(P.gen() - 1)(2))^(-1)).lift()
        else:
            sqrtPower = ((ZZ.quotient(ZZ(norm(P) - 1))(2))^(-1)).lift()
        if sqrtPower == 0:
            sqrtPower = 1            
        a2 = S(E.a2())
        a62 = S(E.a6()/(pi^2))        
        level = _determine_level([a2, a62], pAdics, T, 1)
        if verbose > 0:
            print ("Determining necessary transformation for " +
                   str(T.count_children_at_level(level)) + " cases")
        for node in T.children_at_level(level):
            alphaSqrd = -F(a2(node.representative()))
            betaSqrd = F(-a62(node.representative()))
            alpha = alphaSqrd^sqrtPower
            beta = betaSqrd^sqrtPower
            alphaBetaPair = tuple([alpha, beta])
            if alphaBetaPair in changeDict:
                changeDict[alphaBetaPair].merge(node, from_root=True)
            else:
                Tn = pAdicNode(pAdics=T.pAdics(), width=T.width)
                Tn.merge(node, from_root=True)
                changeDict[alphaBetaPair] = Tn

    # Performing the necessary transformations
    if verbose > 0:
        print "Performing %d transformations"%len(changeDict)
    for (alphaBetaPair, Tn) in changeDict.iteritems():
        En = E.rst_transform(0, F.lift(alphaBetaPair[0]),
                             F.lift(alphaBetaPair[1])*pi)
        result.append(dict(next_step=6+1/2, T=Tn, E=En, E0=E0))
    return result

def _tate_step6(E, S, pAdics, T, E0, **kwds):
    r"""Perform step 6 of Tate's algorithm.

    Stop if the polynomial .. MATH::
    
        X^3 + \frac{a_2}{\pi} X^2 + \frac{a_4}{\pi^2} X +
        \frac{a_6}{\pi^3}

    has three distinct roots in the residue field of the p-adics. Here
    $a_2$, $a_4$ and $a_6$ are the respective invariants of the
    elliptic curve and $\pi$ is the uniformizer of the
    p-adics. Equivalently stop if the valuation of .. MATH::

        -4 a_2^3 a_6 + a_2^2 a_4^2 - 4 a_4^3 - 27 a_6^2 +
        18 a_2 a_4 a_6

    is less than 7. Otherwise continue to step 7.

    In case we stop we have:
    
    - Kodaira symbol: $I_0^*$
    
    - number of components: 5

    INPUT:

    - ``E`` -- The elliptic curve to work on

    - ``S`` -- The polynomial ring over which the coefficients of `E`
      should live

    - ``pAdics`` -- The p-adics to be used

    - ``T`` -- The root of a p-adic tree containing the possible value
      of the variables of `S`

    - ``E0`` -- The current candidate of a minimal model for `E`

    - ``variables`` -- A list of the variables of the polynomial or
      None if it should be determined from `S`
    
    - ``verbose`` -- Verbosity argument

    - ``result`` -- A list of resulting cases to which the cases
      determined by this function should be added.

    - ``precision_cap`` -- A cap on the precision used for the
      variables

    OUTPUT:

    The list given by `result` with some added cases. Added cases
    could include the case in which we stop at step 6 and the case we
    continue onto step 7, but only if some value of the variables
    would give such a case.

    """
    case_big = dict(E=E, next_step=7, E0=E0)
    case_small = dict(E=E, KS="I0*", m=5, E0=E0)
    char = pAdics.characteristic()
    if char != 2:
        case_small['vDelta'] = 6
        case_small['f'] = 2
    D = S(-4*E.a2()^3*E.a6() + E.a2()^2*E.a4()^2 - 4*E.a4()^3 - 27*E.a6()^2 +
          18*E.a2()*E.a4()*E.a6())
    return _get_two_cases_invariant(D, pAdics, T, 7, case_big, case_small,
                                    **kwds)
        
def _tate_step7(E, S, pAdics, T, E0, case, restrictions, **kwds):
    r"""Perform step 7 of Tate's algorithm.

    Stop if the polynomial .. MATH::
    
        X^3 + \frac{a_2}{\pi} X^2 + \frac{a_4}{\pi^2} X +
        \frac{a_6}{\pi^3}

    has one single and one double root in the residue field of the
    p-adics. Here $a_2$, $a_4$ and $a_6$ are the respective invariants
    of the elliptic curve and $\pi$ is the uniformizer of the
    p-adics. Equivalently stop if the valuation of .. MATH::

        3 a_4 - a_2^2

    is less than 3. Otherwise continue to step 8.

    In case we stop we have:
    
    - Kodaira symbol: $I_n^*$

    We also need to perform the subalgorithm for step 7 if the
    characteristic is 2 or we want the order of the group of
    components.

    INPUT:

    - ``E`` -- The elliptic curve to work on

    - ``S`` -- The polynomial ring over which the coefficients of `E`
      should live

    - ``pAdics`` -- The p-adics to be used

    - ``T`` -- The root of a p-adic tree containing the possible value
      of the variables of `S`

    - ``E0`` -- The current candidate of a minimal model for `E`

    - ``variables`` -- A list of the variables of the polynomial or
      None if it should be determined from `S`
    
    - ``verbose`` -- Verbosity argument

    - ``result`` -- A list of resulting cases to which the cases
      determined by this function should be added.

    - ``precision_cap`` -- A cap on the precision used for the
      variables

    OUTPUT:

    The list given by `result` with some added cases. Added cases
    could include the case in which we stop at step 7, the case we
    continue onto step 8 and the case we continue with the step 7
    subalgorithm, but only if some value of the variables would give
    such a case.

    """
    case_big = dict(E=E, next_step=8, E0=E0)
    if pAdics.characteristic() == 2 or \
       'type' in restrictions or \
       _should_calculate_c(case, restrictions):
        case_small = dict(E=E, next_step=7+_encode_quotient(1,0), E0=E0)
    else:
        case_small = dict(E=E, KS="In*", f=2, E0=E0)
    return _get_two_cases_invariant(S(3*E.a4() - (E.a2())^2), pAdics, T, 3,
                                   case_big, case_small, **kwds)

def _encode_quotient(n, b):
    r"""An injective map $\N \times {0,1} \to \Q \cap (0,1)$"""
    m = 2*n + b
    return 1 / (m+1)

def _decode_quotient(q):
    r"""A left inverse of :func:`_encode_quotient`"""
    m = ZZ(1/q) - 1
    if is_even(m):
        n = ZZ(m/2)
        b = 0
    else:
        n = ZZ((m - 1)/2)
        b = 1   
    return n , b
            
def _tate_step7sub_t(E, S, pAdics, T, E0, n, verbose=False, result=[], **kwds):
    r"""Perform the transformation necessary before a step in the
    subalgorithm of step 7 of Tate's algorithm.

    If this is the $n$-th step in the subalgorithm transform the curve
    such that it has a Weierstrass equation of the form .. MATH::

        Y^2 + a_1 X Y + a_3 Y = X^3 + a_2 X^2 + a_4 X + a_6

    for which $a_2$ has valuation precisely 1, $a_3$ has valuation at
    least $(n+4)/2$ if $n$ is even, $a_4$ has valuation at least
    $(n+5)/2$ if $n$ is odd, and $a_6$ has valuation at least $n + 3$.

    INPUT:

    - ``E`` -- The elliptic curve to work on

    - ``S`` -- The polynomial ring over which the coefficients of `E`
      should live

    - ``pAdics`` -- The p-adics to be used

    - ``T`` -- The root of a p-adic tree containing the possible value
      of the variables of `S`

    - ``E0`` -- The current candidate of a minimal model for `E`

    - ``n`` -- The number of the step in the subalgorithm that will be
      performed after this transformation.

    - ``variables`` -- A list of the variables of the polynomial or
      None if it should be determined from `S`
    
    - ``verbose`` -- Verbosity argument

    - ``result`` -- A list of resulting cases to which the cases
      determined by this function should be added.

    - ``precision_cap`` -- A cap on the precision used for the
      variables

    OUTPUT:

    The list given by `result` with some added cases. Added cases
    include the possible transformations to put the elliptic curve in
    the described form with the appropiate values for the variables
    for this to be the case.

    """
    R = pAdics.order()
    P = pAdics.prime_ideal()
    F = pAdics.residue_field()
    pi = pAdics.uniformizer()
    char = pAdics.characteristic()

    # For characteristic 2 compute the integer s
    # such that a^s is the square root of a
    if char == 2:
        if R == ZZ and P in ZZ.ideal_monoid():
            sqrtPower = ((ZZ.quotient(P.gen() - 1)(2))^(-1)).lift()
        else:
            sqrtPower = ((ZZ.quotient(ZZ(norm(P) - 1))(2))^(-1)).lift()
        if sqrtPower == 0:
            sqrtPower = 1

    # Determine the level of nodes responsible for the transformations
    changeDict = dict()
    if n == 1:
        a42 = S(E.a4()/(pi^2))
        if char == 2:
            level = _determine_level([a42], pAdics, T, 1)
        else:
            a21 = S(E.a2()/pi)
            if char == 3:
                level = _determine_level([a21, a42], pAdics, T, 1)
            else:
                a63 = S(E.a6()/(pi^3))
                level = _determine_level([a21, a42, a63], pAdics, T, 1)
    else:
        if is_odd(n):
            k = ZZ((n+1)/2)
            a21 = S(E.a2()/pi)
            if char == 2:
                a6k = S(E.a6()/(pi^(2*k+1)))
                level = _determine_level([a21, a6k], pAdics, T, 1)
            else:
                a4k = S(E.a4()/(pi^(k+1)))
                level = _determine_level([a21, a4k], pAdics, T, 1)
        else:
            k = ZZ((n+2)/2)
            if char == 2:
                a6k = S(E.a6()/(pi^(2*k)))
                level = _determine_level([a6k], pAdics, T, 1)
            else:
                a3k = S(E.a3()/(pi^k))
                level = _determine_level([a3k], pAdics, T, 1)

    # Determine the transformations necessary
    if verbose > 0:
        print ("Determining necessary transformations for " +
               str(T.count_children_at_level(level)) + " cases")
    for node in T.children_at_level(level):
        if n == 1:
            a42_ev = F(a42(node.representative()))
            if char == 2:
                change = a42_ev^sqrtPower
            else:
                a21_ev = F(a21(node.representative()))
                if char == 3:
                    change = -a42_ev / (2 * a21_ev)
                else:
                    a63_ev = F(a63(node.representative()))
                    change = (a21_ev*a42_ev - 9*a63_ev)/(2*(3*a42_ev - a21_ev^2))
        else:
            if is_odd(n):
                a21_ev = F(a21(node.representative()))
                if char == 2:
                    a6k_ev = F(a6k(node.representative()))
                    square = a6k_ev / a21_ev
                    change = square^sqrtPower
                else:
                    a4k_ev = F(a4k(node.representative()))
                    change = - a4k_ev / (2 * a21_ev)
            else:
                if char == 2:
                    a6k_ev = F(a6k(node.representative()))
                    change = a6k_ev^sqrtPower
                else:
                    a3k_ev = F(a3k(node.representative()))
                    change = - a3k_ev / F(2)
                    
        if change in changeDict:
            changeDict[change].merge(node, from_root=True)
        else:
            Tn = pAdicNode(pAdics=T.pAdics(), width=T.width)
            Tn.merge(node, from_root=True)
            changeDict[change] = Tn

    # Performing the necessary transformations
    if verbose > 0: 
        print "Performing %d transformations."%len(changeDict)
    for (change, Tn) in changeDict.iteritems():
        if n==1:
            En = E.rst_transform(pi * F.lift(change), 0, 0)
        elif is_odd(n):
            En = E.rst_transform(pi^k * F.lift(change), 0, 0)
        else:
            En = E.rst_transform(0, 0, pi^k * F.lift(change))
        result.append(dict(next_step=7 + _encode_quotient(n ,1), T=Tn, E=En,
                           E0=E0))
        
    return result
        
def _tate_step7sub(E, S, pAdics, T, E0, n, **kwds):
    r"""Perform a step in the subalgorithm of step 7 of Tate's algorithm.

    In step $n$ of this subalgorithm we have different stopping
    conditions depending on the parity of $n$.

    If $n$ is odd we stop if the polynomial .. MATH::

        X^2 + \frac{a_3}{\pi^{(n+3)/2}}X - \frac{a_6}{\pi^{n+3}}

    has distinct roots over the algebraic closure of the residue field
    of the p-adics, i.e. if the valuation of $a_3^2 + 4 a_6$ is less
    than $n + 4$.

    If $n$ is even we stop if the polynomial .. MATH::

        \frac{a_2}{\pi} X^2 + \frac{a_4}{\pi^{(n+4)/2} X
        + \frac{a_6}{\pi^(n+3)}
    
    has distinct roots over the algebraic closure of the residue field
    of the p-adics, i.e. if the valuation of $a_4^2 - 4*a_2*a_6$ is
    less than $n + 5$.

    In both cases $a_2$, $a_3$, $a_4$ and $a_6$ are the appropiate
    invariants of the elliptic curve and $\pi$ is the uniformizer of
    the p-adics. If we don't stop in a step we continue to the next
    step of the subalgorithm.

    In case we stop in step $n$ of the subalgorithm we have:
    
    - Kodaira symbol: $I_n$
    
    - number of components: n + 5

    INPUT:

    - ``E`` -- The elliptic curve to work on

    - ``S`` -- The polynomial ring over which the coefficients of `E`
      should live

    - ``pAdics`` -- The p-adics to be used

    - ``T`` -- The root of a p-adic tree containing the possible value
      of the variables of `S`

    - ``E0`` -- The current candidate of a minimal model for `E`

    - ``n`` -- The number of the step of the subalgorithm that will be
      performed

    - ``variables`` -- A list of the variables of the polynomial or
      None if it should be determined from `S`
    
    - ``verbose`` -- Verbosity argument

    - ``result`` -- A list of resulting cases to which the cases
      determined by this function should be added.

    - ``precision_cap`` -- A cap on the precision used for the
      variables

    OUTPUT:

    The list given by `result` with some added cases. Added cases
    could include the case in which we stop at this step and the case
    we continue onto the next step, but only if some value of the
    variables would give such a case.

    """
    case_big = dict(E=E, next_step=7+_encode_quotient(n+1,0), E0=E0)
    case_small = dict(E=E, KS="I"+str(n)+"*", m=5+n, E0=E0)
    if is_odd(n):
        return _get_two_cases_invariant(S(E.a3()^2 + 4*E.a6()), pAdics, T,
                                        n + 4, case_big, case_small, **kwds)
    else:
        return _get_two_cases_invariant(S(E.a4()^2 - 4*E.a2()*E.a6()), pAdics,
                                        T, n + 5, case_big, case_small, **kwds)
     
def _tate_step8_t(E, S, pAdics, T, E0, verbose=False, result=[], **kwds):
    r"""Perform the transformation necessary before step 8 of Tate's
    algorithm.

    Transform the curve such that it has a Weierstrass equation of the
    form .. MATH::

        Y^2 + a_1 X Y + a_3 Y = X^3 + a_2 X^2 + a_4 X + a_6

    for which $a_2$ has valuation at least 2, $a_4$ has valuation at
    least 3 and $a_6$ has valuation at least 4.

    INPUT:

    - ``E`` -- The elliptic curve to work on

    - ``S`` -- The polynomial ring over which the coefficients of `E`
      should live

    - ``pAdics`` -- The p-adics to be used

    - ``T`` -- The root of a p-adic tree containing the possible value
      of the variables of `S`

    - ``E0`` -- The current candidate of a minimal model for `E`

    - ``variables`` -- A list of the variables of the polynomial or
      None if it should be determined from `S`
    
    - ``verbose`` -- Verbosity argument

    - ``result`` -- A list of resulting cases to which the cases
      determined by this function should be added.

    - ``precision_cap`` -- A cap on the precision used for the
      variables

    OUTPUT:

    The list given by `result` with some added cases. Added cases
    include the possible transformations to put the elliptic curve in
    the described form with the appropiate values for the variables
    for this to be the case.

    """
    R = pAdics.order()
    P = pAdics.prime_ideal()
    F = pAdics.residue_field()
    pi = pAdics.uniformizer()
    
    if F.characteristic() != 3:
        # If the characteristic is not 3,
        # the transformation is always the same
        result.append(dict(next_step=8+1/2, T=T, E0=E0, 
                           E=E.rst_transform(-E.a2()*F.lift(F(3)^(-1)), 0, 0)))
    else:
        # In characteristic 3
        # Find the integer s such that a^s is the cube root of a
        if R == ZZ and P in ZZ.ideal_monoid():
            cubertPower = ((ZZ.quotient(P.gen() - 1)(3))^(-1)).lift()
        else:
            cubertPower = ((ZZ.quotient(ZZ(norm(P) - 1))(3))^(-1)).lift()

        # Determine the necessary transformations
        changeDict = dict()
        a63 = S(E.a6()/(pi^3))
        level = _determine_level([a63], pAdics, T, 1)
        if verbose > 0:
            print ("Determining necessary transformation for " +
                   str(T.count_children_at_level(level)) + " cases")
        for node in T.children_at_level(level):
            cube = F(a63(node.representative()))
            change = cube^cubertPower
            if change in changeDict:
                changeDict[change].merge(node, from_root=True)
            else:
                Tn = pAdicNode(pAdics=T.pAdics(), width=T.width)
                Tn.merge(node, from_root=True)
                changeDict[change] = Tn

        # Performing the necessary transformations
        if verbose > 0:
            print "Performing %d transformations."%len(changeDict)
        for (change, Tn) in changeDict.iteritems():
            En = E.rst_transform(-pi * F.lift(change), 0, 0)
            result.append(dict(next_step=8+1/2, T=Tn, E=En, E0=E0))
        
    return result
            
def _tate_step8(E, S, pAdics, T, E0, **kwds):
    r"""Perform step 8 of Tate's algorithm.

    Stop if the polynomial .. MATH::
    
        X^2 + \frac{a_3}{\pi^2} X + \frac{a_6}{\pi^4}

    has distinct roots in the algebraic closure of the residue field
    of the p-adics. Equivalently we stop if the valuation of $a_3^2 -
    4 a_6$ is less than 5. Here $a_3$ and $a_6$ are the
    respective invariants of the elliptic curve and $\pi$ is the
    uniformizer of the p-adics. Continue to step 9 otherwise.

    In case we stop we have:
    
    - Kodaira symbol: $IV^*$
    
    - number of components: 7

    INPUT:

    - ``E`` -- The elliptic curve to work on

    - ``S`` -- The polynomial ring over which the coefficients of `E`
      should live

    - ``pAdics`` -- The p-adics to be used

    - ``T`` -- The root of a p-adic tree containing the possible value
      of the variables of `S`

    - ``E0`` -- The current candidate of a minimal model for `E`

    - ``variables`` -- A list of the variables of the polynomial or
      None if it should be determined from `S`
    
    - ``verbose`` -- Verbosity argument

    - ``result`` -- A list of resulting cases to which the cases
      determined by this function should be added.

    - ``precision_cap`` -- A cap on the precision used for the
      variables

    OUTPUT:

    The list given by `result` with some added cases. Added cases
    could include the case in which we stop at step 8 and the case we
    continue onto step 9, but only if some value of the variables
    would give such a case.

    """
    case_big = dict(E=E, next_step=9, E0=E0)
    case_small = dict(E=E, KS="IV*", m=7, E0=E0)
    char = pAdics.characteristic()
    if char != 3:
        case_small['vDelta'] = 8
        case_small['f'] = 2
    return _get_two_cases_invariant(S( ( E.a3() )^2 + 4 * E.a6() ), pAdics, T,
                                   5, case_big, case_small, **kwds)
        
def _tate_step9_t(E, S, pAdics, T, E0, verbose=False, result=[],
                                **kwds):
    r"""Perform the transformation necessary before step 9 of Tate's
    algorithm.

    Transform the curve such that it has a Weierstrass equation of the
    form .. MATH::

        Y^2 + a_1 X Y + a_3 Y = X^3 + a_2 X^2 + a_4 X + a_6

    for which $a_3$ has valuation at least 3 and $a_6$ has valuation
    at least 5.

    INPUT:

    - ``E`` -- The elliptic curve to work on

    - ``S`` -- The polynomial ring over which the coefficients of `E`
      should live

    - ``pAdics`` -- The p-adics to be used

    - ``T`` -- The root of a p-adic tree containing the possible value
      of the variables of `S`

    - ``E0`` -- The current candidate of a minimal model for `E`

    - ``variables`` -- A list of the variables of the polynomial or
      None if it should be determined from `S`
    
    - ``verbose`` -- Verbosity argument

    - ``result`` -- A list of resulting cases to which the cases
      determined by this function should be added.

    - ``precision_cap`` -- A cap on the precision used for the
      variables

    OUTPUT:

    The list given by `result` with some added cases. Added cases
    include the possible transformations to put the elliptic curve in
    the described form with the appropiate values for the variables
    for this to be the case.

    """
    R = pAdics.order()
    P = pAdics.prime_ideal()
    F = pAdics.residue_field()
    pi = pAdics.uniformizer()
    
    if F.characteristic() != 2:
        # If the characteristic is not 2
        # the transformation is always the same
        result.append(dict(next_step=9+1/2, T=T, E0=E0,
                           E=E.rst_transform(0, 0, -E.a3()*F.lift(F(2)^(-1)))))
    else:
        # In characteristic 2
        # Determine the integers s such that a^s is the square root of a
        if R == ZZ and P in ZZ.ideal_monoid():
            sqrtPower = ( ( ZZ.quotient( P.gen() - 1 )(2) )^(-1) ).lift()
        else:
            sqrtPower = ( ( ZZ.quotient( ZZ(norm(P) - 1) )(2) )^(-1) ).lift()
        if sqrtPower == 0:
            sqrtPower = 1

        # Determine all necessary transformations
        changeDict = dict()
        a64 = S(E.a6()/(pi^4))
        level = _determine_level([a64], pAdics, T, 1)
        if verbose > 0:
            print ("Determining necessary transformation for " +
                   str(T.count_children_at_level(level)) + " cases")
        for node in T.children_at_level(level):
            square = -F(a64(node.representative()))
            change = square^sqrtPower
            if change in changeDict:
                changeDict[change].merge(node, from_root=True)
            else:
                Tn = pAdicNode(pAdics=T.pAdics(), width=T.width)
                Tn.merge(node, from_root=True)
                changeDict[change] = Tn

        # Performing all necessary transformations
        if verbose > 0:
            print "Performing %d transformations."%len(changeDict)
        for (change, Tn) in changeDict.iteritems():
            En = E.rst_transform(0, 0, -pi^2 * F.lift(change))
            result.append(dict(next_step=9+1/2, T=Tn, E=En, E0=E0))
        
    return result
            
def _tate_step9(E, S, pAdics, T, E0, **kwds):
    r"""Perform step 9 of Tate's algorithm.

    Stop if the valuation of the invariant $a_4$ of the elliptic curve
    is less than 4. Continue to step 10 otherwise.

    In case we stop we have:
    
    - Kodaira symbol: $III^*$
    
    - number of components: 8

    - order of the group of components: 2

    INPUT:

    - ``E`` -- The elliptic curve to work on

    - ``S`` -- The polynomial ring over which the coefficients of `E`
      should live

    - ``pAdics`` -- The p-adics to be used

    - ``T`` -- The root of a p-adic tree containing the possible value
      of the variables of `S`

    - ``E0`` -- The current candidate of a minimal model for `E`

    - ``variables`` -- A list of the variables of the polynomial or
      None if it should be determined from `S`
    
    - ``verbose`` -- Verbosity argument

    - ``result`` -- A list of resulting cases to which the cases
      determined by this function should be added.

    - ``precision_cap`` -- A cap on the precision used for the
      variables

    OUTPUT:

    The list given by `result` with some added cases. Added cases
    could include the case in which we stop at step 9 and the case we
    continue onto step 10, but only if some value of the variables
    would give such a case.

    """
    case_big = dict(E=E, next_step=10, E0=E0)
    case_small = dict(E=E, KS="III*", m=8, c=2, E0=E0)
    char = pAdics.characteristic()
    if char != 2:
        case_small['vDelta'] = 9
        case_small['f'] = 2
    return _get_two_cases_invariant(S( E.a4() ), pAdics, T, 4, case_big,
                                    case_small, **kwds)
            
def _tate_step10(E, S, pAdics, T, E0, **kwds):
    r"""Perform step 10 of Tate's algorithm.

    Stop if the valuation of the invariant $a_6$ of the elliptic curve
    is less than 6. Continue to step 11 otherwise.

    In case we stop we have:
    
    - Kodaira symbol: $II^*$
    
    - number of components: 9

    - order of the group of components: 1

    INPUT:

    - ``E`` -- The elliptic curve to work on

    - ``S`` -- The polynomial ring over which the coefficients of `E`
      should live

    - ``pAdics`` -- The p-adics to be used

    - ``T`` -- The root of a p-adic tree containing the possible value
      of the variables of `S`

    - ``E0`` -- The current candidate of a minimal model for `E`

    - ``variables`` -- A list of the variables of the polynomial or
      None if it should be determined from `S`
    
    - ``verbose`` -- Verbosity argument

    - ``result`` -- A list of resulting cases to which the cases
      determined by this function should be added.

    - ``precision_cap`` -- A cap on the precision used for the
      variables

    OUTPUT:

    The list given by `result` with some added cases. Added cases
    could include the case in which we stop at step 10 and the case we
    continue onto step 11, but only if some value of the variables
    would give such a case.

    """
    case_big = dict(E=E, next_step=11, E0=E0)
    case_small = dict(E=E, KS="II*", m=9, c=1, E0=E0)
    char = pAdics.characteristic()
    if char != 2 and char != 3:
        case_small['vDelta'] = 10
        case_small['f'] = 2
    return _get_two_cases_invariant(S(E.a6()), pAdics, T, 6,
                                   case_big, case_small, **kwds)
                               
def _tate_step11(E, S, pAdics, T, E0, verbose=False, result=[], **kwds):
    r"""Perform step 1 of Tate's algorithm.

    Rescale the curve and start over at step 1.

    INPUT:

    - ``E`` -- The elliptic curve to work on

    - ``S`` -- The polynomial ring over which the coefficients of `E`
      should live

    - ``pAdics`` -- The p-adics to be used

    - ``T`` -- The root of a p-adic tree containing the possible value
      of the variables of `S`

    - ``E0`` -- The current candidate of a minimal model for `E`

    - ``variables`` -- A list of the variables of the polynomial or
      None if it should be determined from `S`
    
    - ``verbose`` -- Verbosity argument

    - ``result`` -- A list of resulting cases to which the cases
      determined by this function should be added.

    - ``precision_cap`` -- A cap on the precision used for the
      variables

    OUTPUT:

    The list given by `result` with one additional case. This case
    corresponds to the case in which we rescaled the curve and start
    over at step 1.

    """
    if verbose > 0:
        print "Performing final transformation and restarting the algorithm."
    pi = pAdics.uniformizer()
    a1 = S(E.a1()/pi)
    a2 = S(E.a2()/(pi^2))
    a3 = S(E.a3()/(pi^3))
    a4 = S(E.a4()/(pi^4))
    a6 = S(E.a6()/(pi^6))
    E = EllipticCurve([a1,a2,a3,a4,a6])
    result.append(dict(next_step=1, T=T, E=E, E0=E))
    return result
    
def _should_calculate_vDelta(case, restrictions):
    r"""Determine whether one should calculate the valuation of the
    discriminant.

    INPUT:

    - ``case`` -- The case for which this should be determined

    - ``restrictions`` -- Any restrictions on what should be computed

    OUTPUT:

    True if it is necessary to compute the valuation of the
    discriminant. False otherwise.

    """
    return (not case.has_key('vDelta') and
            (len(restrictions) == 0 or 'discriminant' in restrictions or
             _should_calculate_m(case, restrictions) or
             _should_calculate_f(case, restrictions) or
             _should_calculate_n(case, restrictions)))

def _tate_calculate_vDelta(E, S, pAdics, T, case, **kwds):
    r"""Compute the valuation of the discriminant.

    Compute the valuation of the discriminant of the elliptic curve.

    INPUT:

    - ``E`` -- The elliptic curve to work on

    - ``S`` -- The polynomial ring over which the coefficients of `E`
      should live

    - ``pAdics`` -- The p-adics to be used

    - ``T`` -- The root of a p-adic tree containing the possible value
      of the variables of `S`

    - ``variables`` -- A list of the variables of the polynomial or
      None if it should be determined from `S`
    
    - ``verbose`` -- Verbosity argument

    - ``result`` -- A list of resulting cases to which the cases
      determined by this function should be added.

    - ``precision_cap`` -- A cap on the precision used for the
      variables

    OUTPUT:

    The list given by `result` with some added cases. For each
    possible valuation of the discriminant a case is added which
    copies the given case but with the appropiate valuation and the
    values for the variables for which this valuation is attained.

    """
    return _get_cases_invariant(S(E.discriminant()), pAdics, T, 'vDelta', case,
                                **kwds)

def _should_calculate_m(case, restrictions):
    r"""Determine whether one should calculate the number of components.

    INPUT:

    - ``case`` -- The case for which this should be determined

    - ``restrictions`` -- Any restrictions on what should be computed

    OUTPUT:

    True if it is necessary to compute the number of components. False
    otherwise.

    """
    return (not case.has_key('m') and
            (len(restrictions) == 0 or
             _should_calculate_f(case, restrictions)))
    
def _tate_calculate_m(E, S, pAdics, T, case, result=[], **kwds):
    r"""Compute the number of components.

    Compute the number of components of the elliptic curve over the
    algebraic closure of the residue field, counted without
    multiplicity.

    INPUT:

    - ``E`` -- The elliptic curve to work on

    - ``S`` -- The polynomial ring over which the coefficients of `E`
      should live

    - ``pAdics`` -- The p-adics to be used

    - ``T`` -- The root of a p-adic tree containing the possible value
      of the variables of `S`

    - ``variables`` -- A list of the variables of the polynomial or
      None if it should be determined from `S`
    
    - ``verbose`` -- Verbosity argument

    - ``result`` -- A list of resulting cases to which the cases
      determined by this function should be added.

    - ``precision_cap`` -- A cap on the precision used for the
      variables

    OUTPUT:

    The list given by `result` with some added cases. For each
    possible number of components a case is added which copies the
    given case but with the appropiate valuation and the values for
    the variables for which this number is attained.

    """
    KS = case['KS']
    if KS.endswith('*'):
        if KS.startswith('IV'): #IV*
            case['m'] = 7
        elif KS.startswith('III'): #III*
            case['m'] = 8
        elif KS.startswith('II'): #II*
            case['m'] = 9
        elif KS.startswith('I0'): #I0*
            case['m'] = 5
        else: #In*
            case['m'] = case['vDelta'] - 1
    else:
        if KS.startswith('IV'): #IV
            case['m'] = 3
        elif KS.startswith('III'): #III
            case['m'] = 2
        elif KS.startswith('II'): #II
            case['m'] = 1
        elif KS.startswith('I0'): #II
            case['m'] = 1
        else: #In
            case['m'] = case['vDelta']
    result.append(case)
    return result

def _should_calculate_c(case, restrictions):
    r"""Determine whether one should calculate the order of the group of
    components.

    INPUT:

    - ``case`` -- The case for which this should be determined

    - ``restrictions`` -- Any restrictions on what should be computed

    OUTPUT:

    True if it is necessary to compute the order of the group of
    components. False otherwise.

    """
    return (not case.has_key('c') and len(restrictions) == 0)
    
def _tate_calculate_c(E, S, pAdics, T, case, result=[], **kwds):
    r"""Compute the order of the group of components.

    Compute the number of components of the special fiber of the
    elliptic curve that are defined over the residue field of the
    p-adics.

    INPUT:

    - ``E`` -- The elliptic curve to work on

    - ``S`` -- The polynomial ring over which the coefficients of `E`
      should live

    - ``pAdics`` -- The p-adics to be used

    - ``T`` -- The root of a p-adic tree containing the possible value
      of the variables of `S`

    - ``variables`` -- A list of the variables of the polynomial or
      None if it should be determined from `S`
    
    - ``verbose`` -- Verbosity argument

    - ``result`` -- A list of resulting cases to which the cases
      determined by this function should be added.

    - ``precision_cap`` -- A cap on the precision used for the
      variables

    OUTPUT:

    The list given by `result` with some added cases. For each
    possible order of the group of components a case is added which
    copies the given case but with the appropiate valuation and the
    values for the variables for which this order is attained.

    """
    KS = case['KS']
    pi = pAdics.uniformizer()
    if KS.endswith('*'):
        if KS.startswith('IV'): #IV*
            if case.has_key('roots'):
                case['c'] = case['roots'] + 1
            else:
                return _get_number_of_roots_cases([S(1), S(E.a3()/(pi^2)),
                                                   S(-E.a6()/(pi^4))], pAdics,
                                                  T, 'roots', case,
                                                  result=result, **kwds)
        elif KS.startswith('III'): #III*
            case['c'] = 2
        elif KS.startswith('II'): #II*
            case['c'] = 1
        elif KS.startswith('I0'): #I0*
            if case.has_key('roots'):
                case['c'] = case['roots'] + 1
            else:
                return _get_number_of_roots_cases([S(1), S(E.a2()/pi),
                                                   S(E.a4()/(pi^2)),
                                                   S(E.a6()/(pi^3))], pAdics,
                                                  T, 'roots', case,
                                                  result=result, **kwds)
        else: #In*
            if case.has_key('roots'):
                case['c'] = case['roots'] + 2
            else:
                n = Integer(KS[1:-1])
                if is_odd(n):
                    k = ZZ((n+3)/2)
                    return _get_number_of_roots_cases([S(1),
                                                       S(E.a3()/(pi^(k))),
                                                       S(-E.a6()/(pi^(2*k)))],
                                                      pAdics, T, 'roots', case,
                                                      result=result, **kwds)
                else:
                    k = ZZ((n+2)/2)
                    return _get_number_of_roots_cases([S(E.a2()/pi),
                                                       S(E.a4()/(pi^(k+1))),
                                                       S(E.a6()/(pi^(2*k+1)))],
                                                      pAdics, T, 'roots', case,
                                                      result=result, **kwds)
    else:
        if KS.startswith('IV'): #IV
            if case.has_key('roots'):
                case['c'] = case['roots'] + 1
            else:
                return _get_number_of_roots_cases([S(1), S(E.a3()/pi),
                                                   S(-E.a6()/(pi^2))], pAdics,
                                                  T, 'roots', case,
                                                  result=result, **kwds)
        elif KS.startswith('III'): #III
            case['c'] = 2
        elif KS.startswith('II'): #II
            case['c'] = 1
        elif KS.startswith('I0'): #II
            case['c'] = 1
        else: #In
            if case['split']:
                case['c'] = case['vDelta']
            else:
                case['c'] = (1 if is_odd(case['vDelta']) else 2)

    result.append(case)
    return result

def _should_calculate_f(case, restrictions):
    r"""Determine whether one should calculate the conductor exponent.

    INPUT:

    - ``case`` -- The case for which this should be determined

    - ``restrictions`` -- Any restrictions on what should be computed

    OUTPUT:

    True if it is necessary to compute the conductor exponent. False
    otherwise.

    """
    return (not case.has_key('f') and (len(restrictions) == 0 or
                                       'conductor' in restrictions or
                                       'reduction_type' in restrictions))
    
def _tate_calculate_f(E, S, pAdics, T, case, result=[], **kwds):
    r"""Compute the conductor exponent.

    Compute exponent of the conductor of the elliptic curve at the
    prime of the p-adics.

    INPUT:

    - ``E`` -- The elliptic curve to work on

    - ``S`` -- The polynomial ring over which the coefficients of `E`
      should live

    - ``pAdics`` -- The p-adics to be used

    - ``T`` -- The root of a p-adic tree containing the possible value
      of the variables of `S`

    - ``variables`` -- A list of the variables of the polynomial or
      None if it should be determined from `S`
    
    - ``verbose`` -- Verbosity argument

    - ``result`` -- A list of resulting cases to which the cases
      determined by this function should be added.

    - ``precision_cap`` -- A cap on the precision used for the
      variables

    OUTPUT:

    The list given by `result` with some added cases. For each
    possible exponent of the conductor a case is added which copies
    the given case but with the appropiate valuation and the values
    for the variables for which this exponent is attained.

    """
    case['f'] = case['vDelta'] - case['m'] + 1
    result.append(case)
    return result

def _should_calculate_n(case, restrictions):
    r"""Determine whether one should calculate the number $n$ in the
    Kodaira symbol.

    INPUT:

    - ``case`` -- The case for which this should be determined

    - ``restrictions`` -- Any restrictions on what should be computed

    OUTPUT:

    True if it is necessary to compute the number $n$ in the Kodaira
    symbol. False otherwise.

    """
    return (case['KS'].count('n') > 0 and (len(restrictions) == 0 or
                                           'type' in restrictions))
    
def _tate_calculate_n(E, S, pAdics, T, case, result=[], **kwds):
    r"""Compute the number $n$ in $I_n$ or $I_n^*$.

    Compute the number $n$ if the elliptic curve at the prime of the
    p-adics has Kodaira symbol $I_n$ or $I_n^*$.

    INPUT:

    - ``E`` -- The elliptic curve to work on

    - ``S`` -- The polynomial ring over which the coefficients of `E`
      should live

    - ``pAdics`` -- The p-adics to be used

    - ``T`` -- The root of a p-adic tree containing the possible value
      of the variables of `S`

    - ``variables`` -- A list of the variables of the polynomial or
      None if it should be determined from `S`
    
    - ``verbose`` -- Verbosity argument

    - ``result`` -- A list of resulting cases to which the cases
      determined by this function should be added.

    - ``precision_cap`` -- A cap on the precision used for the
      variables

    OUTPUT:

    The list given by `result` with some added cases. For each
    possible $n$ a case is added which copies the given case but with
    the appropiate valuation and the values for the variables for
    which this $n$ is attained.

    """
    KS = case['KS']
    if KS.endswith('*'): #In*
        case['KS'] = KS.replace('n', str(case['vDelta']-6))
    else: #In
        case['KS'] = KS.replace('n', str(case['vDelta']))
    result.append(case)
    return result

def _should_calculate_split(case, restrictions):
    r"""Determine whether one should calculate whether the reduction is
    split.

    INPUT:

    - ``case`` -- The case for which this should be determined

    - ``restrictions`` -- Any restrictions on what should be computed

    OUTPUT:

    True if it is necessary to compute whether the reduction is
    split. False otherwise.

    """
    return (case['f'] == 1 and not case.has_key('split') and
            (_should_calculate_c(case, restrictions) or
             'reduction_type' in restrictions))

def _tate_calculate_split(E, S, pAdics, T, case, result=[], **kwds):
    r"""Compute if split or non-split multiplicative reduction.

    INPUT:

    - ``E`` -- The elliptic curve to work on

    - ``S`` -- The polynomial ring over which the coefficients of `E`
      should live

    - ``pAdics`` -- The p-adics to be used

    - ``T`` -- The root of a p-adic tree containing the possible value
      of the variables of `S`

    - ``variables`` -- A list of the variables of the polynomial or
      None if it should be determined from `S`
    
    - ``verbose`` -- Verbosity argument

    - ``result`` -- A list of resulting cases to which the cases
      determined by this function should be added.

    - ``precision_cap`` -- A cap on the precision used for the
      variables

    OUTPUT:

    The list given by `result` with some added cases. If the elliptic
    curve can have split multiplicative reduction at the prime of the
    p-adics, adds a case for that with the appropiate values for the
    variables. If the elliptic curve can have non-split multiplicative
    reduction at the prime of the p-adics, adds a case for that with
    the appropiate values for the variables.

    """
    if case.has_key('roots'):
        if case['roots'] > 0:
            case['split'] = True
        else:
            case['split'] = False
        result.append(case)
        return result
    else:
        return _get_number_of_roots_cases([S(1), S(E.a1()), S(-E.a2())],
                                          pAdics, T, 'roots', case,
                                          result=result, **kwds)
    
def _tate_finish(case, restrictions, result=[], variables=None, **kwds):
    r"""Turn a case into a final result

    INPUT:

    - ``case`` -- The case to be finalized
    
    - ``restrictions`` -- The restrictions on what should be computed

    - ``result`` -- A list to which the final result should be appended

    - ``variables`` -- The variables in the coefficients of the
      elliptic curve.

    OUTPUT:

    The given list 'result' to which we appended a tuple consisting of
    the information needed in the final result and a pAdicTree object
    that contains the values for the variables necessary to get this
    result.

    """
    tree = pAdicTree(variables=variables, root=case['T'])
    if len(restrictions) == 0:
        f = case['f']
        if f == 0:
            red_type = None
        elif f == 1:
            if case['split']:
                red_type = 1
            else:
                red_type = -1
        else:
            red_type = 0
        myresult = FreyCurveLocalData(case['E0'],
                                      case['T'].pAdics().prime_ideal(), f,
                                      case['vDelta'],
                                      KodairaSymbol(case['KS']), case['c'],
                                      red_type)
    else:
        myresult = []
        for r in restrictions:
            if r == 'conductor':
                myresult.append(case['f'])
            if r == 'reduction_type':
                f = case['f']
                if f == 0:
                    myresult.append(None)
                elif f == 1:
                    if case['split']:
                        myresult.append(1)
                    else:
                        myresult.append(-1)
                else:
                    myresult.append(0)
            if r == 'discriminant':
                myresult.append(case['vDelta'])
            if r == 'type':
                myresult.append(KodairaSymbol(case['KS']))
            if r == 'minimal_model':
                myresult.append(case['E0'])
    result.append((myresult, tree))
    return result
           
def _tate_cleanup(cases):
    r"""Cleanup the final result to return

    INPUT:

    - ``cases`` -- A list of pairs consisting of possible return
      values and a pAdicTree containing the values of the variables
      necessary to get those return values.

    OUTPUT:

    The result of the function as a ConditionalValue

    """
    result = []
    for case in cases:
        flag = True
        for case0 in result:
            if case0[0] == case[0]:
                # We can merge here to prevent unneccesary copying.
                # Since we would discard both old trees anyways this
                # is not a problem.
                case0[1].pAdic_tree()._root.merge(case[1]._root)
                flag = False
                break
        if flag:
            result.append((case[0], TreeCondition(case[1])))
    return ConditionalValue(result)

def _check_elliptic_curve(E):
   r"""Check whether input is an elliptic curve"""
   if not isinstance(E, EllipticCurve_generic):
       raise ValueError("%s is not an elliptic curve."%(E,))

def _init_coefficient_ring(coefficient_ring, E):
    r"""Initialize the coefficient ring

    INPUT:

    - ``coefficient_ring`` -- The argument coefficient ring

    - ``E`` -- The elliptic curve

    OUTPUT:

    The coefficient ring to be used

    """
    if coefficient_ring is None:
        coefficient_ring = E.base_ring()
    for a in E.a_invariants():
        if a not in coefficient_ring:
            raise ValueError("%s is not part of %s."%(a, coefficient_ring))
    return coefficient_ring

def _init_pAdics(pAdics, ring, prime, coefficient_ring):
    if pAdics is None:
        if ring is None:
            ring = coefficient_ring.base_ring()
        if prime is None:
            raise ValueError("At least the argument pAdics or " +
                             "the argument prime should be given.")
        pAdics = pAdicBase(ring, prime)
    if not isinstance(pAdics, pAdicBase):
        raise ValueError("%s is not a pAdicBase object."%(pAdics,))
    return pAdics
 
def _init_polynomial_ring(coefficient_ring, pAdics):
    return coefficient_ring.change_ring(pAdics.number_field())
    
def _init_variables_tate(polynomial_ring):
    return list(polynomial_ring.gens())
    
def _init_initial_values(initial_values, pAdics, variables):
    if initial_values is None:
        initial_values = pAdicTree(pAdics=pAdics, full=True,
                                   variables=variables)
    if not isinstance(initial_values, pAdicTree):
        raise ValueError("%s is not a p-adic tree."%(initial_value,))
    if not pAdics.is_extension_of(initial_values.pAdics()):
        raise ValueError(str(pAdics) + " does not extend the p-adics of " +
                         str(initial_values))
    return initial_values
    
def _init_cases(T, E):
    firstCase = dict(next_step=1, T=T.root(), E=E, E0=E)
    return [firstCase], []
    
def _init_str_list(str_list):
    if isinstance(str_list, str) or not hasattr(str_list, '__iter__'):
        str_list = [str_list]
    for s in str_list:
        if not isinstance(s, str):
            raise ValueError("%s is not a string."%(s,))
    return str_list
