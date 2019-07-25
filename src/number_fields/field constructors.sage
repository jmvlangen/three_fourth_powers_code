r"""Ways of constructing fields.

Some special methods to construct fields that have uniform output.
These methods include a function to construct the field extension
created by adding a root, a function to construct the composite field
of two fields and a function 

EXAMPLES:

We can build field extensions by adding roots::

    sage: K1.<a> = field_with_root(QQ, 2); K1
    Number Field in a with defining polynomial x^2 - 2
    sage: K2.<b> = field_with_root(K1, 3); K2
    Number Field in b with defining polynomial x^4 - 10*x^2 + 1
    sage: K3.<c> = field_with_root(K2, 6); K3
    Number Field in b with defining polynomial x^4 - 10*x^2 + 1

We can find the fixed field of some galois elements::

    sage: L = CyclotomicField(24)
    sage: G = L.galois_group()
    sage: fixed_field([G[1], G[4]])
    Number Field in zeta240 with defining polynomial x^2 - 2
    sage: fixed_field([G[5]])
    Number Field in zeta240 with defining polynomial x^4 - 4*x^2 + 1

We can find the composite field of two number fields, even if one of
them is $\Q$::

    sage: K1.<a> = QuadraticField(-7)
    sage: K2.<b> = CyclotomicField(24)
    sage: K3.<c> = QQ[sqrt(2), sqrt(3)]
    sage: composite_field(K1, K2)
    Number Field in ab with defining polynomial x^16 + 56*x^14 + 1370*x^12 + 19236*x^10 + 169739*x^8 + 960036*x^6 + 3382958*x^4 + 6637820*x^2 + 5536609
    sage: composite_field(K1, K3)
    Number Field in asqrt2 with defining polynomial x^8 + 8*x^6 + 256*x^4 + 3648*x^2 + 14400
    sage: composite_field(K2, K3)
    Cyclotomic Field of order 24 and degree 8
    sage: composite_field(QQ, K3)
    Number Field in sqrt2 with defining polynomial x^2 - 2 over its base field
    sage: composite_field(QQ, K2)
    Cyclotomic Field of order 24 and degree 8

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

def field_with_root(K, a, names='sqrt_a', give_embedding=False):
    r"""Get a field extension of K that contains the specified root.

    INPUT:
    
    - ``K`` -- A number field, which may be the rationals.

    - ``a`` -- An element of the number field K.

    - ``names`` -- A string (default: 'sqrt_a') or list thereof
      indicating the name(s) to use for the generators of the bigger
      field.

    - ``give_embedding`` -- A boolean (default: False) that indicates
      whether embeddings of K into this field and a square root of `a`
      should be returned.
    
    OUPUT:

    A number field that contains `K` and a square root of `a`. If it
    is an extension of `K` and not `K` itself its generators will have
    the names specified by names. If give_embeddings was set to True,
    will return a tuple consisting of: the number field as mentioned
    before; an embedding of K into that number field; and a square
    root of `a` inside that number field

    EXAMPLES:

    Simple examples over $\Q$::
    
        sage: field_with_root(QQ, 3)
        Number Field in sqrt_a with defining polynomial x^2 - 3
        sage: field_with_root(QQ, -2)
        Number Field in sqrt_a with defining polynomial x^2 + 2
    
    Working over a bigger field also works::

        sage: K = CyclotomicField(5); K
        Cyclotomic Field of order 5 and degree 4
        sage: field_with_root(K, -2, names='a')
        Number Field in a with defining polynomial x^8 - 2*x^7 + 11*x^6 - 16*x^5 + 39*x^4 - 28*x^3 + 19*x^2 + 6*x + 11

    The root might already be contained in the field::

        sage: K = CyclotomicField(5); K
        Cyclotomic Field of order 5 and degree 4
        sage: field_with_root(K, 5)
        Cyclotomic Field of order 5 and degree 4
        sage: K(5).is_square()
        True

    A map can also be generated::

        sage: K = CyclotomicField(3); K
        Cyclotomic Field of order 3 and degree 2
        sage: field_with_root(K, -2, names='a', give_embedding=True)
        (Number Field in a with defining polynomial x^4 - 2*x^3 + 7*x^2 - 6*x + 3,
         Ring morphism:
           From: Cyclotomic Field of order 3 and degree 2
           To:   Number Field in a with defining polynomial x^4 - 2*x^3 + 7*x^2 - 6*x + 3
           Defn: zeta3 |--> 2/5*a^3 - 3/5*a^2 + 2*a - 7/5,
         2/5*a^3 - 3/5*a^2 + 2*a - 2/5)

    """
    a = K(a)
    if a.is_square():
        if give_embedding:
            return K, K.hom(K), sqrt(a)
        else:
            return K
    else:
        R.<x> = K[]
        L = K.extension(x^2 - a, names=names).absolute_field(names=names)
        if give_embedding:
            K_to_L = K.embeddings(L)[0]
            return L, K_to_L, sqrt(K_to_L(a))
        else:
            return L

def fixed_field(H):
    r"""Return the fixed field of a subset of a galois group

    INPUT:

    - ``H`` -- An iterable object containing elements of a galois
      group. len(H) should be at least 1

    OUTPUT:

    A number field K consisting of all those elements that are mapped
    to themselves by elements of H.

    EXAMPLES:

    A simple example::

        sage: K = CyclotomicField(12)
        sage: G = K.galois_group()
        sage: H = [G.gens()[0]]
        sage: fixed_field(H)
        Number Field in zeta120 with defining polynomial x^2 - 2*x + 4

    If H only contains the trivial element, the entire field is
    returned::

        sage: K = CyclotomicField(12)
        sage: G = K.galois_group()
        sage: H = [G.identity()]
        sage: fixed_field(H)
        Cyclotomic Field of order 12 and degree 4

    H empty does not work::

        sage: fixed_field([])
        Traceback (most recent call last)
        ...
        IndexError: list index out of range

    If H generates or is the entire galois group we get the rational
    field::

        sage: K = CyclotomicField(24)
        sage: G = K.galois_group()
        sage: fixed_field(G)
        Rational Field
        sage: fixed_field(G.gens())
        Rational Field

    """
    G = H[0].parent()
    if H == G:
        return QQ
    if hasattr(H, 'fixed_field'):
        result = H.fixed_field()
        if isinstance(result, tuple):
            return result[0]
        else:
            return result
    return fixed_field(G.subgroup(H))

@cached_function
def composite_field(K1, K2, give_maps=False):
    r"""Return the composite field of K1 and K2

    INPUT:

    - ``K1`` -- A number field, which may be the rationals.

    - ``K2`` -- A number field, which may be the rationals.

    - ``give_maps`` -- A boolean (default=False) indicating whether
      the embeddings should be returned.

    OUTPUT:

    A number field K that is the composite field of K1 and K2. If
    give_maps was set to True, will instead return a tuple consisting
    of: the field K; an embedding of K1 into K; and an embedding of K2
    into K

    EXAMPLES:

    Combining two quadratic fields::

        sage: K1 = QuadraticField(2)
        sage: K2 = QuadraticField(3)
        sage: K = composite_field(K1, K2); K
        Number Field in a0 with defining polynomial x^4 - 10*x^2 + 1
        sage: K(2).is_square() and K(3).is_square()
        True

    Also works if one of the fields contains the other::

        sage: K1 = QuadraticField(2)
        sage: K2 = CyclotomicField(8)
        sage: K = composite_field(K1, K2); K
        Cyclotomic Field of order 8 and degree 4
        sage: K2(2).is_square()
        True

    Can use the optional give_maps to obtain the embeddings::

        sage: K1 = QuadraticField(2)
        sage: K2 = QuadraticField(3)
        sage: composite_field(K1, K2, give_maps=True)
        (Number Field in a0 with defining polynomial x^4 - 10*x^2 + 1, Ring morphism:
           From: Number Field in a with defining polynomial x^2 - 2
           To:   Number Field in a0 with defining polynomial x^4 - 10*x^2 + 1
           Defn: a |--> -1/2*a0^3 + 9/2*a0, Ring morphism:
           From: Number Field in a with defining polynomial x^2 - 3
           To:   Number Field in a0 with defining polynomial x^4 - 10*x^2 + 1
           Defn: a |--> -1/2*a0^3 + 11/2*a0)

    """
    if not is_field(K1):
        K1 = K1.fraction_field()
    if not is_field(K2):
        K2 = K2.fraction_field()
    if K2.absolute_degree() < K1.absolute_degree():
        if give_maps:
            K, K2_to_K, K1_to_K = composite_field(K2, K1, give_maps=True)
            return K, K1_to_K, K2_to_K
        else:
            return composite_field(K2, K1)
    R = K1.embeddings(K2)
    if len(R) == 0:
        if give_maps:
            return K1.composite_fields(K2, both_maps=give_maps)[0][0:3]
        else:
            return K1.composite_fields(K2)[0]
    else:
        if give_maps:
            return K2, R[0], K2.hom(K2)
        else:
            return K2
