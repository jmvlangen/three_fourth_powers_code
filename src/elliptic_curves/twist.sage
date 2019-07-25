r"""Implements twisting methods for elliptic curves

This file contains two main methods. The first :func:`is_twist`
determines whether two curves are twists of one another. The second
:func:`twist_elliptic_curve` computes the twist of an elliptic curve
by some element.

EXAMPLES::

    sage: E1 = EllipticCurve([1, 1]); E1
    Elliptic Curve defined by y^2 = x^3 + x + 1 over Rational Field
    sage: E2 = twist_elliptic_curve(E1, 2); E2
    Elliptic Curve defined by y^2 = x^3 + 4*x + 8 over Rational Field
    sage: is_twist(E1, E2)
    -1

One can also work over number fields::

    sage: K.<v> = CyclotomicField(7)
    sage: E1 = EllipticCurve([v, 1 + v^2]); E1
    Elliptic Curve defined by y^2 = x^3 + v*x + (v^2+1) over Cyclotomic Field of order 7 and degree 6
    sage: E2 = twist_elliptic_curve(E1, 7); E2
    Elliptic Curve defined by y^2 = x^3 + 49*v*x + (343*v^2+343) over Cyclotomic Field of order 7 and degree 6
    sage: is_twist(E1, E2)
    -1
    sage: E3 = twist_elliptic_curve(E1, -7); E3
    Elliptic Curve defined by y^2 = x^3 + 49*v*x + (-343*v^2-343) over Cyclotomic Field of order 7 and degree 6
    sage: is_twist(E1, E3)
    1

The methods also work over polynomial rings, or rather over their
field of fractions::

    sage: R.<a> = QQ[]
    sage: E1 = EllipticCurve([a+1, a^2 + 2*a - 4]); E1
    Elliptic Curve defined by y^2 = x^3 + (a+1)*x + (a^2+2*a-4) over Univariate Polynomial Ring in a over Rational Field
    sage: E2 = twist_elliptic_curve(E1, (a - 1)); E2
    Elliptic Curve defined by y^2 = x^3 + (a^3-a^2-a+1)*x + (a^5-a^4-7*a^3+17*a^2-14*a+4) over Univariate Polynomial Ring in a over Rational Field
    sage: is_twist(E1, E2)
    -1

AUTHORS:

- Joey van Langen (2019-02-14): initial version

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

def _is_twist_good_char(E1, E2):
    """Determine whether the curve E1 is a twist of E2.

    INPUT:

    - ``E1`` -- An elliptic curve over a field of characteristic not 2
      or 3.

    - ``E2`` -- An elliptic curve defined over the same field as E1.
    
    OUTPUT:

    1 if the two curves are isomorphic.

    -1 if the curves are twists of one another, but not isomorphic
    over their base field.

    0 if the curves are not twists of one another.

    """
    if E1.c4()^3 * E2.c6()^2 != E2.c4()^3 * E1.c6()^2:
        return 0
    if E2.c4() == 0:
        c = E1.c6() / E2.c6()
        try:
            a = c.nth_root(3)
            if a.is_square():
                return 1
            else:
                return -1
        except ValueError:
            return 0
    elif E2.c6() == 0:
        b = E1.c4() / E2.c4()
        try:
            a = b.nth_root(2)
            if a.is_square():
                return 1
            else:
                return -1
        except ValueError:
            return 0
    else:
        b = E1.c4() / E2.c4()
        c = E1.c6() / E2.c6()
        a = c / b
        if a.is_square():
            return 1
        else:
            return -1

def _is_twist_char_2(E1, E2):
    """Determine whether the curve E1 is a twist of E2.

    INPUT:

    - ``E1`` -- An elliptic curve over a field of characteristic 2.

    - ``E2`` -- An elliptic curve defined over the same field as E1.
    
    OUTPUT:

    1 if the two curves are isomorphic.

    -1 if the curves are twists of one another, but not isomorphic
    over their base field.

    0 if the curves are not twists of one another.

    """
    if (E1.a1() != 0 or E1.a3() != 0 or E2.a1() != 0 or E2.a3() != 0):
        return 0
    b1 = E1.a2()^2 + E1.a4()
    b2 = E2.a2()^2 + E2.a4()
    c1 = E1.a2()*E1.a4() + E1.a6()
    c2 = E2.a2()*E2.a4() + E2.a6()
    if b1^3 * c2^2 != b2^3 * c1^2:
        return 0
    if b2 == 0:
        c = c1 / c2
        try:
            a = c.nth_root(3)
            if a.is_square():
                return 1
            else:
                return -1
        except ValueError:
            return 0
    elif c2 == 0:
        b = b1 / b2
        try:
            a = b.nth_root(2)
            if a.is_square():
                return 1
            else:
                return -1
        except ValueError:
            return 0
    else:
        b = b1 / b2
        c = c1 / c2
        a = c / b
        if a.is_square():
            return 1
        else:
            return -1    

def _is_twist_char_3(E1, E2):
    """Determine whether the curve E1 is a twist of E2.

    INPUT:

    - ``E1`` -- An elliptic curve over a field of characteristic 3.

    - ``E2`` -- An elliptic curve defined over the same field as E1.
    
    OUTPUT:

    1 if the two curves are isomorphic.

    -1 if the curves are twists of one another, but not isomorphic
    over their base field.

    0 if the curves are not twists of one another.

    """
    if (E1.b2()^2 * E2.b4() != E2.b2()^2 * E1.b4() or
        E1.b2()^3 * E2.b6() != E2.b2()^2 * E1.b6() or
        E1.b4()^3 * E2.b4()^2 != E2.b4()^3 * E1.b6()^2):
        return 0
    if E2.b2() == 0:
        if E2.b4() == 0:
            c = E1.b6() / E2.b6()
            try:
                a = c.nth_root(3)
                if a.is_square():
                    return 1
                else:
                    return -1
            except ValueError:
                return 0
        elif E2.b6() == 0:
            b = E1.b4() / E2.b4()
            try:
                a = b.nth_root(2)
                if a.is_square():
                    return 1
                else:
                    return -1
            except ValueError:
                return 0
        else:
            b = E1.b4() / E2.b4()
            c = E1.b6() / E2.b6()
            a = c / b
            if a.is_square():
                return 1
            else:
                return -1
    else:
        a = E1.b2() / E2.b2()
        if a.is_square():
            return 1
        else:
            return -1

def is_twist(E1, E2):
    """Determine whether the curve E1 is a twist of E2.

    INPUT:

    - ``E1`` -- An elliptic curve over a field.

    - ``E2`` -- An elliptic curve defined over the same field as E1.
    
    OUTPUT:

    1 if the two curves are isomorphic.

    -1 if the curves are twists of one another, but not isomorphic
    over their base field.

    0 if the curves are not twists of one another.

    EXAMPLE::

        sage: E1 = EllipticCurve([1, 1])
        sage: E2 = EllipticCurve([2, 4])
        sage: E3 = EllipticCurve([4, 8])
        sage: E4 = EllipticCurve([16, 64])
        sage: is_twist(E1, E2) # not twists
        0
        sage: is_twist(E1, E3) # twists, but not isomorphic
        -1
        sage: is_twist(E1, E4) # isomorphic
        1

    """
    p = E1.base_ring().characteristic()
    if p == 2:
        return _is_twist_char_2(E1, E2)
    elif p == 3:
        return _is_twist_char_3(E1, E2)
    else:
        return _is_twist_good_char(E1, E2)

def twist_elliptic_curve(E, d):
    """Give the twist of an elliptic curve by 'd'.

    Twisting an elliptic curve with Weierstrass equation ..MATH::
    
        y^2 = x^3 + a_2 x^2 + a_4 x + a_6

    means changing it into the curve given by ..MATH::
    
        y^2 = x^3 + d a_2 x^2 + d^2 a_4 x + d^3 a_6

    which is isomorphic to the first curve over $R(\\sqrt{d})$, where
    $R$ is the ring over which the curve was defined.

    INPUT:

    - ``E`` -- An elliptic curve given by a Weierstrass equation with
               $a_1 = 0$ and $a_3 = 0$

    - ``d`` -- A ring element that can be multiplied with the
               coefficients of E. In general this will be an element
               of the base ring of E, but any ring for which coercion
               with those elements is defined should work.

    OUTPUT:
    
    An elliptic curve that is the twist of the given curve E by the
    parameter d.

    EXAMPLES:
    
    A simple example::

        sage: E = EllipticCurve([1,2]); E
        Elliptic Curve defined by y^2 = x^3 + x + 2 over Rational Field
        sage: twist_elliptic_curve(E,-1)
        Elliptic Curve defined by y^2 = x^3 + x - 2 over Rational Field

    An example over a more complicated field ::

        sage: K = CyclotomicField(5)
        sage: K.<zeta> = CyclotomicField(5)
        sage: E = EllipticCurve([zeta,3]); E
        Elliptic Curve defined by y^2 = x^3 + zeta*x + 3 over Cyclotomic Field of order 5 and degree 4
        sage: twist_elliptic_curve(E, zeta)
        Elliptic Curve defined by y^2 = x^3 + zeta^3*x + 3*zeta^3 over Cyclotomic Field of order 5 and degree 4

    We can also twist using parameters ::

        sage: R.<a> = QQ[]
        sage: E = EllipticCurve([a^2 + 3, a-1]); E
        Elliptic Curve defined by y^2 = x^3 + (a^2+3)*x + (a-1) over Univariate Polynomial Ring in a over Rational Field
        sage: twist_elliptic_curve(E, a+1)
        Elliptic Curve defined by y^2 = x^3 + (a^4+2*a^3+4*a^2+6*a+3)*x + (a^4+2*a^3-2*a-1) over Univariate Polynomial Ring in a over Rational Field

    """
    if E.a1() != 0 or E.a3() != 0:
        raise ValueError("Can only twist if a1 and a3 are zero.")
    a2 = d   * E.a2()
    a4 = d^2 * E.a4()
    a6 = d^3 * E.a6()
    return EllipticCurve([0,a2,0,a4,a6])
