r"""Function to express a symmetric polynomial in terms of the
standard symmetric polynomials.

EXAMPLE::

    sage: R.<x,y,z> = QQ[]
    sage: f = x^2 + y^2 + z^2
    sage: g = polynomial_to_symmetric(f); g
    s1^2 - 2*s2
    sage: g(x + y + z, x*y + x*z + y*z, x*y*z) == f
    True

AUTHORS:

- Joey van Langen (2019-02-15): initial version

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

def polynomial_to_symmetric(polynomial, names=None):
    r"""Represent a polynomial in terms of the symmetric polynomials.

    INPUT:

    - ``polynomial`` -- A symmetric polynomial in any number of
      variables.

    - ``names`` -- A list of names for the symmetric polynomials. This
      list must have length n, where n is the number of variables in
      the parent of the given polynomial. By default will use the
      names s1, s2, s3, up to n.

    OUTPUT:
    
    A polynomial that when evaluated on the symmetric polynomials in
    which the given polynomial lives, returns the given polynomial.

    EXAMPLE::

        sage: R.<x,y,z> = QQ[]
        sage: f = x^2 + y^2 + z^2
        sage: g = polynomial_to_symmetric(f); g
        s1^2 - 2*s2
        sage: g(x + y + z, x*y + x*z + y*z, x*y*z) == f
        True

    """
    R = polynomial.parent().base_ring()
    n = polynomial.parent().ngens()
    sym = SymmetricFunctions(R)
    f = sym.from_polynomial(polynomial)
    if names is None:
        names = ['s%s'%(i,) for i in range(1,n+1)]
    if len(names) != n:
        raise ValueError('The length of names is not %s'%(n,))
    S = PolynomialRing(R, names=names)
    gens = S.gens()
    g = sum(coeff * product((gens[i-1] if (i >= 1 and i <= n) else 0)
                            for i in partition)
            for partition, coeff in list(sym.elementary()(f)))
    return S(g)
