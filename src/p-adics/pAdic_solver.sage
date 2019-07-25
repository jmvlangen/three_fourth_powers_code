r"""Methods for finding solutions to polynomial equations over local
fields

Given a polynomial with coefficients in some number field and a finite
prime P, can compute the roots of this polynomial in the completion at
P up to a certain precision and return the result as a p-adic tree.

EXAMPLES::

    sage: R.<x,y> = QQ[]
    sage: f = x^2 + y^2 - 1
    sage: T, _ = find_pAdic_roots(f, prime=3, precision=2)
    sage: T.children_at_level(2)
    [p-adic node represented by (6, 1) with 9 children,
     p-adic node represented by (3, 1) with 9 children,
     p-adic node represented by (0, 1) with 9 children,
     p-adic node represented by (8, 0) with 9 children,
     p-adic node represented by (8, 3) with 9 children,
     p-adic node represented by (8, 6) with 9 children,
     p-adic node represented by (1, 3) with 9 children,
     p-adic node represented by (1, 0) with 9 children,
     p-adic node represented by (1, 6) with 9 children,
     p-adic node represented by (3, 8) with 9 children,
     p-adic node represented by (0, 8) with 9 children,
     p-adic node represented by (6, 8) with 9 children]

Working with coefficients with negative valuation::

    sage: R.<x, y> = QQ[]
    sage: f = x^2 / 9 + y^3 / 27
    sage: T1, _ = find_pAdic_roots(f, prime = 2, precision=2)
    sage: T1.children_at_level(2)
    [p-adic node represented by (0, 2) with 4 children,
     p-adic node represented by (2, 0) with 4 children,
     p-adic node represented by (0, 0) with 4 children,
     p-adic node represented by (2, 2) with 4 children,
     p-adic node represented by (3, 1) with 4 children,
     p-adic node represented by (1, 1) with 4 children]
    sage: T2, _ = find_pAdic_roots(f, prime=3, precision=1)
    sage: T2.minimum_full_level()
    2
    sage: T2.children_at_level(2)
    [p-adic node represented by (3, 6) with 9 children,
     p-adic node represented by (0, 0) with 9 children,
     p-adic node represented by (6, 6) with 9 children]
    sage: T3, _ = find_pAdic_roots(f, prime=3, precision=-1)
    sage: T3.minimum_full_level()
    1
    sage: T3.children_at_level(1)
    [p-adic node represented by (0, 0) with 9 children]

Different ways of giving the p-adics::

    sage: R.<x, y> = ZZ[]
    sage: f = y^2 - x^3 - 1
    sage: T1, _ = find_pAdic_roots(f, pAdics=pAdicBase(QQ, 5), precision=2)
    sage: T2, _ = find_pAdic_roots(f, ring=QQ, prime=5, precision=2)
    sage: T3, _ = find_pAdic_roots(f, prime=5, precision=2)
    sage: T1 == T2
    True
    sage: T1 == T3
    True

If variables are not specified it only takes into account
variables that actually occur::

    sage: R.<x,y> = QQ[]
    sage: f = x^2 + x + 1
    sage: T1, _ = find_pAdic_roots(f, prime=3, precision=2)
    sage: T1.width
    1
    sage: T2, _ = find_pAdic_roots(f, prime=3, variables=(x,y), precision=2)
    sage: T2.width
    2

Using an initial tree to limit the possibilities::

    sage: R.<x,y> = QQ[]
    sage: f = y^2 - x^3
    sage: pAdics = pAdicBase(QQ, 5)
    sage: N = pAdicNode(pAdics=pAdics, width=2, full=True)
    sage: N.children.remove_by_coefficients((0,0))
    sage: T, _ = find_pAdic_roots(f, pAdics=pAdics, value_tree=N, precision=2)
    sage: T.children_at_level(2)
    [p-adic node represented by (24, 7) with 25 children,
     p-adic node represented by (9, 2) with 25 children,
     p-adic node represented by (19, 22) with 25 children,
     p-adic node represented by (4, 17) with 25 children,
     p-adic node represented by (14, 12) with 25 children,
     p-adic node represented by (21, 19) with 25 children,
     p-adic node represented by (6, 4) with 25 children,
     p-adic node represented by (16, 14) with 25 children,
     p-adic node represented by (11, 9) with 25 children,
     p-adic node represented by (1, 24) with 25 children,
     p-adic node represented by (21, 6) with 25 children,
     p-adic node represented by (16, 11) with 25 children,
     p-adic node represented by (1, 1) with 25 children,
     p-adic node represented by (11, 16) with 25 children,
     p-adic node represented by (6, 21) with 25 children,
     p-adic node represented by (19, 3) with 25 children,
     p-adic node represented by (4, 8) with 25 children,
     p-adic node represented by (9, 23) with 25 children,
     p-adic node represented by (24, 18) with 25 children,
     p-adic node represented by (14, 13) with 25 children]

Letting $K$ be a strict subfield of $L$::

    sage: L.<z> = CyclotomicField(3)
    sage: R.<x,y> = L[]
    sage: f = x^2 + z*x*y + z^2*y^2
    sage: pAdics = pAdicBase(L, L.prime_above(3))
    sage: N = pAdicNode(pAdics=pAdics.pAdics_below(QQ), width=2, full=True)
    sage: T, _ = find_pAdic_roots(f, pAdics=pAdics, value_tree=N, precision=4)
    sage: T.children_at_level(2)
    [p-adic node represented by (0, 3) with 9 children,
     p-adic node represented by (3, 6) with 9 children,
     p-adic node represented by (0, 0) with 9 children,
     p-adic node represented by (6, 3) with 9 children,
     p-adic node represented by (0, 6) with 9 children,
     p-adic node represented by (6, 0) with 9 children,
     p-adic node represented by (6, 6) with 9 children,
     p-adic node represented by (3, 0) with 9 children,
     p-adic node represented by (3, 3) with 9 children,
     p-adic node represented by (1, 1) with 9 children,
     p-adic node represented by (4, 4) with 9 children,
     p-adic node represented by (7, 7) with 9 children,
     p-adic node represented by (2, 2) with 9 children,
     p-adic node represented by (5, 5) with 9 children,
     p-adic node represented by (8, 8) with 9 children]

Using the `precision_cap` argument::

    sage: R.<x,y> = QQ[]
    sage: f = y^3 - x^2 - x*y
    sage: T, _ = find_pAdic_roots(f, prime=3, precision_cap=2)
    Warning: Lowering precision on root to 2 to accomodate for precision cap 2 on variables
    sage: T.children_at_level(2)
    [p-adic node represented by (0, 3) with 9 children,
     p-adic node represented by (3, 6) with 9 children,
     p-adic node represented by (0, 0) with 9 children,
     p-adic node represented by (6, 3) with 9 children,
     p-adic node represented by (0, 6) with 9 children,
     p-adic node represented by (6, 0) with 9 children,
     p-adic node represented by (6, 6) with 9 children,
     p-adic node represented by (3, 0) with 9 children,
     p-adic node represented by (3, 3) with 9 children,
     p-adic node represented by (8, 2) with 9 children,
     p-adic node represented by (5, 2) with 9 children,
     p-adic node represented by (2, 2) with 9 children]

The special output when using the argument `give_list`. Note that
the first values are not, the second are only roots
modulo 2 and the third are roots modulo 4::

    sage: R.<x,y> = QQ[]
    sage: f = x^2 + y^2 - 4
    sage: Tls, s = find_pAdic_roots(f, prime=2, precision=2, give_list=True)
    sage: s
    0
    sage: Tls[0].children_at_level(2)
    [p-adic node represented by (0, 1) with 4 children,
     p-adic node represented by (2, 1) with 4 children,
     p-adic node represented by (0, 3) with 4 children,
     p-adic node represented by (2, 3) with 4 children,
     p-adic node represented by (1, 0) with 4 children,
     p-adic node represented by (3, 0) with 4 children,
     p-adic node represented by (1, 2) with 4 children,
     p-adic node represented by (3, 2) with 4 children]
    sage: Tls[1].children_at_level(2)
    [p-adic node represented by (1, 1) with 4 children,
     p-adic node represented by (3, 1) with 4 children,
     p-adic node represented by (1, 3) with 4 children,
     p-adic node represented by (3, 3) with 4 children]
    sage: Tls[2].children_at_level(2)
    [p-adic node represented by (0, 2) with 4 children,
     p-adic node represented by (2, 0) with 4 children,
     p-adic node represented by (0, 0) with 4 children,
     p-adic node represented by (2, 2) with 4 children]

AUTHORS:

- Joey van Langen (2019-02-26): initial version

"""

# ****************************************************************************
#       Copyright (C) 2019 Joey van Langen <j.m.van.langen@vu.nl>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from sage.all import Infinity

from sage.rings.polynomial.multi_polynomial import MPolynomial
from sage.rings.polynomial.polynomial_element import Polynomial

def find_pAdic_roots(polynomial, pAdics=None, ring=None, prime=None,
                    variables=None, value_tree=None, precision=20,
                    precision_cap=20, give_list=False, verbose=False):
    r"""Find the p-adic roots of a polynomial up to some precision.

    We consider an extension of number fields $L / K$ and finite
    primes $P$ and $Q$ of $K$ and $L$ respectively such that $Q$ is
    above $P$. Now a polynomial $f(x_1, \ldots, x_n) \in L[x_1,
    \ldots, x_n]$ evaluated at some integral values $a_1, \ldots, a_n$
    in the completion $K_P$ will give some value in $L_Q$. In
    particular we can look for those $a_1, \ldots, a_n$ that are roots
    of $f$ in $L_Q$.

    Furthermore we can look for those $a_1, \ldots, a_n$ that are
    roots up to a certain precision $n$, i.e. such that the valuation
    of $f(a_1, \ldots, a_n)$ at $Q$ is at least $n$. The last is
    precisely what this function does.

    Note that both $L$ and $K$ may be the rationals.
    
    INPUT:
    
    - ``polynomial`` -- A polynomial (in several variables) over the
      field $L$ or a subring thereof.

    - ``pAdics`` -- A pAdicBase object or None (default: None). If not
      None it should give the p-adics to be used, i.e. those defined
      by $L$ and $Q$. If None it will be determined using the
      arguments `ring` and `prime`.
      
    - ``ring`` -- A ring or None (default: None). If not None the
      field of fractions of this ring should be $L$. If None it will
      be determined using the argument `pAdics` or the base ring of
      the argument `polynomial`.

    - ``prime`` -- A prime ideal, a generator thereof or None
      (default: None). If not None the prime ideal should be an
      integral prime ideal of $L$ or a generator thereof. If None the
      argument `pAdics` should be provided and it will be initialized
      as the prime thereof.
      
    - ``variables`` -- A list of variables or None (default:
      None). These should be the variables of the given polynomial. If
      set to None will be initialized as the variables of the given
      argument `polynomial` with the method :meth:`variables`. Note
      that the latter will not consider variables that do not appear
      in the polynomial.
    
    - ``value_tree`` -- A p-adic tree or None (default: None). If not
      None the p-adic tree may be given as a :class:`pAdicNode` which
      is the root of the tree or as a :class:`pAdicTree`. The p-adic
      tree should contain the possible values for the variables. The
      p-adics of the tree should be those defined by $K$ and $P$. If
      set to None this will be initialized as the full p-adic tree
      with the same p-adics as given in the argument `pAdics`.
      
    - ``precision`` -- An integer (default: 20) determining the
      precision $n$ up to which roots should be found.

    - ``precision_cap'' -- A non-negative integer (default:20). This
      gives a cap on the precision used for the variables. If set to
      $m$ then the value of each variable will not be determined
      beyond modulo $P^m$. Since this might lower the precision of the
      root found, the function will print a warning to stdout if this
      happens.

    - ``give_list`` -- A boolean value (default: False), indicating
      whether the result should be either two trees or a list of
      possibilities.
      
    - ``verbose`` -- A boolean value or an integer (default: False).
      When set to True or any value larger then zero will print
      comments to stdout about the computations being done whilst
      busy. If set to False or 0 will not print such comments. If set
      to any negative value will also prevent the printing of any
      warnings. The number of comments increases with a higher value.
      
    OUTPUT:
    
    A tuple consisting of
    
    - The root of a p-adic tree containing all the tuples of p-adic
      values in the given tree such that the valuation of the given
      polynomial at these values is at least the given precision.
      
    - The root of a p-adic tree containing all the tuples of p-adic
      values in the given tree that are not in the first tree
      returned, i.e. for which the valuation of the given polynomial
      at those values is less then the given precision.
      
    If, however, the option give_list was set to True the output will
    be a tuple consisting of
    
    - A list in which each entry is the root of a p-adic tree. The
      $i$-th entry of this list contains the p-adic values such that
      the polynomial evaluated at those values has valuation precisely
      $i + s$ for some fixed $s$ (see second return value). The only
      exception to this rule is the last entry for which the
      polynomial at the values has valuation at least the given
      precision. The list may also be empty.

    - An integer $s$ which gives the lowest precision smaller than the
      given precision in which roots can be found. If no such
      precision exists the return value will be Infinity and the
      returned list is empty.

    EXAMPLES::

        sage: R.<x,y> = QQ[]
        sage: f = x^2 + y^2 - 1
        sage: Ty, Tn = find_pAdic_roots(f, prime=3, precision=2)
        sage: Ty.children_at_level(2)
        [p-adic node represented by (6, 1) with 9 children,
         p-adic node represented by (3, 1) with 9 children,
         p-adic node represented by (0, 1) with 9 children,
         p-adic node represented by (8, 0) with 9 children,
         p-adic node represented by (8, 3) with 9 children,
         p-adic node represented by (8, 6) with 9 children,
         p-adic node represented by (1, 3) with 9 children,
         p-adic node represented by (1, 0) with 9 children,
         p-adic node represented by (1, 6) with 9 children,
         p-adic node represented by (3, 8) with 9 children,
         p-adic node represented by (0, 8) with 9 children,
         p-adic node represented by (6, 8) with 9 children]

    Working with coefficients with negative valuation::

        sage: R.<x, y> = QQ[]
        sage: f = x^2 / 9 + y^3 / 27
        sage: T1, _ = find_pAdic_roots(f, prime = 2, precision=2)
        sage: T1.children_at_level(2)
        [p-adic node represented by (0, 2) with 4 children,
         p-adic node represented by (2, 0) with 4 children,
         p-adic node represented by (0, 0) with 4 children,
         p-adic node represented by (2, 2) with 4 children,
         p-adic node represented by (3, 1) with 4 children,
         p-adic node represented by (1, 1) with 4 children]
        sage: T2, _ = find_pAdic_roots(f, prime=3, precision=1)
        sage: T2.minimum_full_level()
        2
        sage: T2.children_at_level(2)
        [p-adic node represented by (3, 6) with 9 children,
         p-adic node represented by (0, 0) with 9 children,
         p-adic node represented by (6, 6) with 9 children]
        sage: T3, _ = find_pAdic_roots(f, prime=3, precision=-1)
        sage: T3.minimum_full_level()
        1
        sage: T3.children_at_level(1)
        [p-adic node represented by (0, 0) with 9 children]

    Different ways of giving the p-adics::

        sage: R.<x, y> = ZZ[]
        sage: f = y^2 - x^3 - 1
        sage: T1, _ = find_pAdic_roots(f, pAdics=pAdicBase(QQ, 5), precision=2)
        sage: T2, _ = find_pAdic_roots(f, ring=QQ, prime=5, precision=2)
        sage: T3, _ = find_pAdic_roots(f, prime=5, precision=2)
        sage: T1 == T2
        True
        sage: T1 == T3
        True

    If variables are not specified it only takes into account
    variables that actually occur::

        sage: R.<x,y> = QQ[]
        sage: f = x^2 + x + 1
        sage: T1, _ = find_pAdic_roots(f, prime=3, precision=2)
        sage: T1.width
        1
        sage: T2, _ = find_pAdic_roots(f, prime=3, variables=(x,y), precision=2)
        sage: T2.width
        2

    Using an initial tree to limit the possibilities::

        sage: R.<x,y> = QQ[]
        sage: f = y^2 - x^3
        sage: pAdics = pAdicBase(QQ, 5)
        sage: N = pAdicNode(pAdics=pAdics, width=2, full=True)
        sage: N.children.remove_by_coefficients((0,0))
        sage: T, _ = find_pAdic_roots(f, pAdics=pAdics, value_tree=N, precision=2)
        sage: T.children_at_level(2)
        [p-adic node represented by (24, 7) with 25 children,
         p-adic node represented by (9, 2) with 25 children,
         p-adic node represented by (19, 22) with 25 children,
         p-adic node represented by (4, 17) with 25 children,
         p-adic node represented by (14, 12) with 25 children,
         p-adic node represented by (21, 19) with 25 children,
         p-adic node represented by (6, 4) with 25 children,
         p-adic node represented by (16, 14) with 25 children,
         p-adic node represented by (11, 9) with 25 children,
         p-adic node represented by (1, 24) with 25 children,
         p-adic node represented by (21, 6) with 25 children,
         p-adic node represented by (16, 11) with 25 children,
         p-adic node represented by (1, 1) with 25 children,
         p-adic node represented by (11, 16) with 25 children,
         p-adic node represented by (6, 21) with 25 children,
         p-adic node represented by (19, 3) with 25 children,
         p-adic node represented by (4, 8) with 25 children,
         p-adic node represented by (9, 23) with 25 children,
         p-adic node represented by (24, 18) with 25 children,
         p-adic node represented by (14, 13) with 25 children]

    Letting $K$ be a strict subfield of $L$::

        sage: L.<z> = CyclotomicField(3)
        sage: R.<x,y> = L[]
        sage: f = x^2 + z*x*y + z^2*y^2
        sage: pAdics = pAdicBase(L, L.prime_above(3))
        sage: N = pAdicNode(pAdics=pAdics.pAdics_below(QQ), width=2, full=True)
        sage: T, _ = find_pAdic_roots(f, pAdics=pAdics, value_tree=N, precision=4)
        sage: T.children_at_level(2)
        [p-adic node represented by (0, 3) with 9 children,
         p-adic node represented by (3, 6) with 9 children,
         p-adic node represented by (0, 0) with 9 children,
         p-adic node represented by (6, 3) with 9 children,
         p-adic node represented by (0, 6) with 9 children,
         p-adic node represented by (6, 0) with 9 children,
         p-adic node represented by (6, 6) with 9 children,
         p-adic node represented by (3, 0) with 9 children,
         p-adic node represented by (3, 3) with 9 children,
         p-adic node represented by (1, 1) with 9 children,
         p-adic node represented by (4, 4) with 9 children,
         p-adic node represented by (7, 7) with 9 children,
         p-adic node represented by (2, 2) with 9 children,
         p-adic node represented by (5, 5) with 9 children,
         p-adic node represented by (8, 8) with 9 children]

    Using the `precision_cap` argument::

        sage: R.<x,y> = QQ[]
        sage: f = y^3 - x^2 - x*y
        sage: T, _ = find_pAdic_roots(f, prime=3, precision_cap=2)
        Warning: Lowering precision on root to 2 to accomodate for precision cap 2 on variables
        sage: T.children_at_level(2)
        [p-adic node represented by (0, 3) with 9 children,
         p-adic node represented by (3, 6) with 9 children,
         p-adic node represented by (0, 0) with 9 children,
         p-adic node represented by (6, 3) with 9 children,
         p-adic node represented by (0, 6) with 9 children,
         p-adic node represented by (6, 0) with 9 children,
         p-adic node represented by (6, 6) with 9 children,
         p-adic node represented by (3, 0) with 9 children,
         p-adic node represented by (3, 3) with 9 children,
         p-adic node represented by (8, 2) with 9 children,
         p-adic node represented by (5, 2) with 9 children,
         p-adic node represented by (2, 2) with 9 children]

    The special output when using the argument `give_list`. Note that
    the first values are roots modulo 4, the second are only roots
    modulo 2 and the third are not roots at all::

        sage: R.<x,y> = QQ[]
        sage: f = x^2 + y^2 - 4
        sage: Tls, s = find_pAdic_roots(f, prime=2, precision=2, give_list=True)
        sage: s
        0
        sage: Tls[0].children_at_level(2)
        [p-adic node represented by (0, 1) with 4 children,
         p-adic node represented by (2, 1) with 4 children,
         p-adic node represented by (0, 3) with 4 children,
         p-adic node represented by (2, 3) with 4 children,
         p-adic node represented by (1, 0) with 4 children,
         p-adic node represented by (3, 0) with 4 children,
         p-adic node represented by (1, 2) with 4 children,
         p-adic node represented by (3, 2) with 4 children]
        sage: Tls[1].children_at_level(2)
        [p-adic node represented by (1, 1) with 4 children,
         p-adic node represented by (3, 1) with 4 children,
         p-adic node represented by (1, 3) with 4 children,
         p-adic node represented by (3, 3) with 4 children]
        sage: Tls[2].children_at_level(2)
        [p-adic node represented by (0, 2) with 4 children,
         p-adic node represented by (2, 0) with 4 children,
         p-adic node represented by (0, 0) with 4 children,
         p-adic node represented by (2, 2) with 4 children]

    """
    _check_polynomial(polynomial)
    variables = _init_variables(variables, polynomial)
    pAdics = _init_pAdics(pAdics, ring, prime, polynomial)
    value_tree = _init_value_tree(value_tree, pAdics, variables)
    polynomial, least_power = _modify_polynomial(polynomial, pAdics, variables)
    multiplicity = pAdics.extension_multiplicity(value_tree.pAdics())
    precision, var_precision = _init_precision(precision, precision_cap,
                                               least_power, multiplicity,
                                               verbose)
    polynomial_derivatives = _init_derivatives(polynomial, variables)

    if verbose > 0:
        print ("Finding roots of " + str(polynomial) + " modulo " +
               str(pAdics.prime_ideal()._repr_short()) + "^" + str(precision))
       
    result = _find_pAdic_roots(polynomial, polynomial_derivatives, value_tree,
                               precision, var_precision, multiplicity, pAdics,
                               verbose=(verbose-1 if verbose > 0 else verbose),
                               give_list=give_list,
                               quit_on_empty=give_list)
    if give_list:
        return result, least_power
    else:
        return result

def _pAdic_fill_in_check(f, T, prec, pAdics, verbose=False):
    r"""Find the roots of a polynomial at level 1

    INPUT:

    - ``f`` -- The polynomial

    - ``T`` -- The p-adic tree of possible values for the variables

    - ``prec`` -- The precision up to which nodes of level 1 can be
      roots

    - ``pAdics`` -- The p-adics of the bigger field

    - ``verbose`` -- Verbosity argument

    OUTPUT:

    - The p-adic tree of nodes that form roots up to `prec`

    - The p-adic tree of the other nodes in the given tree

    """
    if verbose > 0:
        print "Checking for roots at level 1"
    Tno = pAdicNode(pAdics=T.pAdics(), width=T.width)
    for node in T.children_at_level(1):
        if pAdics.valuation(f(node.representative())) < prec:
            Tno.merge(node, from_root=True)
            node.remove()
    return T, Tno

def _pAdic_convert_function(pAdics1, pAdics2, step_size):
    r"""The explicit implementation of a vector space structure.

    If P is the maximal ideal of the smaller local field and S is the
    ring of integers of the bigger local field, then S / P is a vector
    space over the residue field of P. This can be made explicit by
    using the exact sequence .. MATH::

       S / Q \to S / Q^n \to S / Q^(n-1)

    where $Q$ is the prime above $P$ in $S$. If $Q^n$ divides $P$ then
    this sequence is an exact sequence of vector spaces over the
    residue field of $P$ giving a splitting. Using the vector space
    structure of $S / Q$ over this residue field we thus get an
    explicit basis.

    This function uses such an explicit basis to convert an element of
    the number field associated to the first p-adics into a vector of
    $F^n$ where $F$ is the residue field of $P$.

    INPUT:

    - ``pAdics1`` -- The p-adics of the bigger field
    
    - ``pAdics2`` -- The p-adics of the smaller field
    
    - ``step_size`` -- The length of power series

    OUTPUT:

    A function that takes as input an element of the number field of
    `pAdics1` and outputs a vector in $F^n$ such that if the input
    represented an element of $S / P$, then the output is the
    corresponding vector under some fixed isomorphism.

    """
    phi = pAdics1.extension_vector_space(pAdics2)
    F = pAdics1.residue_field()
    G = pAdics2.residue_field()
    def result(a):
        b = pAdics1.power_series(a, precision=step_size)
        d = []
        for c in b:
            d.extend(list(phi(c)))
        return (G^len(d))(d)
    return result
        
def _pAdic_hensel_check(f, fder, T, level, step_size, pAdics, verbose=False):
    r"""Find the roots of a polynomial at a level using hensel lifting

    INPUT:

    - ``f`` -- The polynomial

    - ``fder`` -- A list of the derivatives of the polynomial
    
    - ``T`` -- The p-adic tree of possible values for the variables

    - ``level`` -- The level of nodes to be checked as roots

    - ``step_size`` -- The additional precision one extra level of
      nodes should provide

    - ``pAdics`` -- The p-adics of the bigger field

    - ``verbose`` -- Verbosity argument

    OUTPUT:

    - The p-adic tree of nodes that form roots up to an additional
      precision of `step_size`

    - The p-adic tree of the other nodes in the given tree

    """
    if verbose > 0:
        print "Checking for roots at level %d"%level
    Tyes = pAdicNode(pAdics=T.pAdics(), width=T.width)
    phi = _pAdic_convert_function(pAdics, T.pAdics(), step_size)
    F = T.pAdics().residue_field()
    pi = T.pAdics().uniformizer()
    if verbose > 1:
        print "Start loop of %d cycles"%T.count_children_at_level(level-1)
    for node in T.children_at_level(level - 1):
        fa = phi(f(node.representative())/(pi^(level-1)))
        fdera = [phi(fderi(node.representative())) for fderi in fder]
        M = matrix(fdera)
        try:
            c = M.solve_left(-fa)
            for c0 in M.kernel():
                cfs = tuple([F.lift(ci) for ci in (c+c0)])
                if node.children.contains(cfs):
                    child = node.children.get(cfs)
                    Tyes.merge(child, from_root=True)
                    child.remove()
        except ValueError:
            pass
    return Tyes, T
    
def _pAdic_level_check(f, fder, T, level, step_size, pAdics, verbose=False):
    r"""Find the roots of a polynomial at a level

    INPUT:

    - ``f`` -- The polynomial

    - ``fder`` -- A list of the derivatives of the polynomial
    
    - ``T`` -- The p-adic tree of possible values for the variables

    - ``level`` -- The level of nodes to be checked as roots

    - ``step_size`` -- The additional precision one extra level of
      nodes should provide

    - ``pAdics`` -- The p-adics of the bigger field

    - ``verbose`` -- Verbosity argument

    OUTPUT:

    - The p-adic tree of nodes that form roots up to an additional
      precision of `step_size`

    - The p-adic tree of the other nodes in the given tree

    """
    if level <= 0:
        return (T,)
    if level == 1:
        return _pAdic_fill_in_check(f, T, step_size, pAdics, verbose=verbose)
    if level > 1:
        return _pAdic_hensel_check(f, fder, T, level, step_size, pAdics,
                                      verbose=verbose)
    raise ValueError("The level %s is not valid."%level)
        
def _find_pAdic_roots(f, fder, T, prec, var_prec, m, pAdics, verbose=False,
                     give_list=False, quit_on_empty=False):
    r"""The recursive implementation of :func:`find_pAdic_roots`

    INPUT:

    - ``f`` -- The polynomial

    - ``fder`` -- A list of the derivatives of the polynomial
    
    - ``T`` -- The p-adic tree of possible values for the variables

    - ``prec`` -- The precision up to which roots should be determined

    - ``var_prec`` -- The level up to which nodes of the tree should
      be used to achieve the precision, i.e. the precision on the
      variables

    - ``m`` -- The valuation of the prime of the smaller p-adics in
      the bigger p-adics.

    - ``pAdics`` -- The p-adics of the bigger field

    - ``verbose`` -- Verbosity argument

    - ``give_list`` -- True if the returned value should be a list,
      False (default) if it should be just two trees.

    - ``quit_on_empty`` -- True if the function should stop if the
      tree is empty, False (default) to keep calculating with an empty
      tree.

    OUTPUT:

    A similar output as the function :func:`find_pAdic_roots`, except
    without the `give_list` argument.

    """
    if give_list:
        Tno = []
    else:
        Tno = pAdicNode(pAdics=T.pAdics(), width=T.width)
    if prec > 0:
        for level in range(1,var_prec+1):
            if T.is_empty():
                if quit_on_empty or not give_list:
                    if give_list:
                        return Tno
                    else:
                        return T, Tno
                level_result = (T,T)
            else:
                step_size = min(m, prec-m*(level-1))
                level_result = _pAdic_level_check(f, fder, T, level, step_size,
                                                  pAdics, verbose=verbose)
            T = level_result[0]
            if len(level_result) > 1:
                if give_list:
                    Tno.append(level_result[1])
                else:
                    Tno.merge(level_result[1])
    if give_list:
        Tno.append(T)
        return Tno
    else:
        return T, Tno
        
def _check_polynomial(polynomial):
    r"""Check whether the polynomial is a polynomial

    INPUT::

    - ``polynomial`` -- The polynomial

    """
    if (not isinstance(polynomial, Polynomial) and
        not isinstance(polynomial, MPolynomial)):
         raise ValueError("%s is not a polynomial."%(polynomial,))
    
def _init_variables(variables, polynomial):
    r"""Initialize the variables and return them

    INPUT:

    - ``variables`` -- The argument variables

    - ``polynomial`` -- The polynomial

    OUTPUT:

    A list of variables in the polynomial

    """
    if variables is None:
        variables = polynomial.variables()
    if not hasattr(variables, '__iter__'):
        raise ValueError("%s is not a list of variables"%(variables,))
    for v in polynomial.variables():
        if v not in variables:
            raise ValueError(str(v) + " is a variable of the polynomial," +
                             " but not listed as a variable")
    return variables
    
def _init_pAdics(pAdics, ring, prime, polynomial):
    r"""Initialize the p-adics and return them

    INPUT:

    - ``pAdics`` -- The argument pAdics

    - ``ring`` -- The argument ring

    - ``prime`` -- The argument prime

    - ``polynomial`` -- The polynomial

    OUTPUT:

    The p-adics to use for the polynomial.

    """
    if pAdics is None:
        if ring is None:
            ring = polynomial.base_ring()
        if prime is None:
            raise ValueError("At least the argument pAdics or " +
                             "the argument prime should be given.")
        pAdics = pAdicBase(ring, prime)
    if not isinstance(pAdics, pAdicBase):
        raise ValueError("%s is not a pAdicBase object."%(pAdics,))
    return pAdics
    
def _init_value_tree(value_tree, pAdics, variables):
    r"""Initialize a p-adic tree of values and return it

    INPUT:

    - ``value_tree`` -- The argument value_tree

    - ``pAdics`` -- The p-adics to be used for the polynomial

    - ``variables`` -- The variables of the polynomial

    OUTPUT:

    The root of a p-adic tree containing possible values for the
    variables.

    """
    if value_tree is None:
        value_tree = pAdicNode(pAdics=pAdics, full=True, width=len(variables))
    if isinstance(value_tree, pAdicTree):
        value_tree = value_tree.root()
    if not isinstance(value_tree, pAdicNode):
        raise ValueError(str(value_tree) +
                         " does not define a valid p-adic tree.")
    if not pAdics.is_extension_of(value_tree.pAdics()):
        raise ValueError("%s does not match the p-adics of %s."%(pAdics,
                                                                 value_tree))
    if value_tree.width != len(variables):
        raise ValueError(str(value_tree) + " does not have as many entries " +
                         "as there are variables")
    return value_tree

def _modify_polynomial(polynomial, pAdics, variables):
    r"""Make the polynomial integral with respect to the prime of the
    p-adics

    This function finds the minimal valuation among the coefficients
    of the polynomial and rescales the polynomial such that this
    valuation is zero.

    INPUT:

    - ``polynomial`` -- The polynomial

    - ``pAdics`` -- The p-adics to be used for the polynomial

    - ``variables`` -- The variables of the polynomial

    OUTPUT:

    - The polynomial rescaled by some $c$ such that the polynomial is
      either $0$ or the minimal valuation among its coefficients is
      $0$.

    - The minimal valuation of the coefficients of the original
      polynomial or Infinity if the original polynomial was $0$.

    """
    S = PolynomialRing(pAdics.number_field(), variables)
    polynomial = S(polynomial)
    least_power = min([Infinity] +
                      [pAdics.valuation(c) for c in polynomial.coefficients()])
    if least_power < Infinity:
        polynomial = pAdics.uniformizer()^(-least_power) * polynomial
    return polynomial, least_power
           
def _init_precision(precision, precision_cap, least_power, multiplicity,
                    verbose):
    r""""Initialize the precision and return it
    
    The returned precision will take into account:

    - The given precision cap on the variables

    - The change in the polynomial to make it integral
     
    - The multiplicity of the two p-adics at play

    INPUT:

    - ``precision`` -- The argument precision

    - ``precision_cap`` -- The argument precision_cap

    - ``least_power`` -- The minimal valuation of the coefficients of
      the original polynomial.

    - ``multiplicity`` -- The multiplicity of the two primes

    - ``verbose`` -- Verbosity argument

    OUTPUT:

    - The precision required on the rescaled polynomial

    - The maximal level required for nodes in the tree of values of
      the variables.

    """
    if not precision in ZZ:
        raise ValueError("The precision should be an integer, not " +
                         str(precision))
    if not precision_cap in ZZ:
        raise ValueError("The precision cap should be an integer, not " +
                         str(precision_cap))
    precision = precision - least_power
    if precision > multiplicity * precision_cap and verbose >= 0:
        precision = multiplicity * precision_cap
        print ("Warning: Lowering precision on root to " +
               str(precision+least_power) +
               " to accomodate for precision cap " + str(precision_cap) +
               " on variables")
    if precision < 0:
        precision = -1
    return precision, ceil(precision/multiplicity)
    
def _init_derivatives(polynomial, variables):
    r"""Calculate the derivatives of the polynomial

    INPUT:

    - ``polynomial`` -- The polynomial

    - ``variables`` -- The variables of the polynomial

    OUTPUT:

    A list of the derivatives of the polynomial to each respective
    variable.

    """
    result = []
    for v in variables:
        v = polynomial.parent()(v)
        result.append(polynomial.derivative(v))
    return result
