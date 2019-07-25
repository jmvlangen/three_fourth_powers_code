r"""Code to work with galois homomorphisms

This code provides methods to change the definition field of a galois
homomorphism. Besides that it also contains code to convert galois
homomorphisms of $\Q(\zeta_N)$ into the corresponding elements of
$(\Z/N\Z)^*$ and back. There is also a method to see how a galois
group acts on the units of the field.

EXAMPLES:

We can extend and restrict galois homomorphisms in towers of number
fields, but the construction only works well in one direction::

    sage: K1 = QuadraticField(3)
    sage: K2 = CyclotomicField(12)
    sage: G1.<s> = K1.galois_group()
    sage: G2.<t,u> = K2.galois_group()
    sage: galois_field_extend(s, K2) == t
    True
    sage: galois_field_restrict(t, K1) == s
    True
    sage: galois_field_restrict(u, K1) == s
    True

The method :func:`galois_field_change` finds the best way to convert
between two fields::

    sage: K1 = QuadraticField(3)
    sage: K2 = CyclotomicField(12)
    sage: K3 = CyclotomicField(20)
    sage: G1.<s> = K1.galois_group()
    sage: G2.<t,u> = K2.galois_group()
    sage: G3.<v,w> = K3.galois_group()
    sage: galois_field_change(s, K2) == t
    True
    sage: galois_field_change(v, K2) == u
    True
    sage: galois_field_change(u, K3) == v^2
    True

For cyclotomic fields we can jump back and forth::

    sage: N = 120
    sage: n = 19
    sage: s = cyclotomic_galois_isomorphism(n, N=N); s
    (1,15)(2,16)(3,13)(4,14)(5,11)(6,12)(7,9)(8,10)(17,31)(18,32)(19,29)(20,30)(21,27)(22,28)(23,25)(24,26)
    sage: cyclotomic_galois_isomorphism(s, N=N)
    19

We can inspect how the galois group acts on the units of a number
field::

    sage: K = QuadraticField(3)
    sage: G.<s> = K.galois_group()
    sage: d = galois_on_units(K)
    sage: U(s(product(U.gens()[i]^exp[i] for i in range(2))))
    u0*u1^2
    sage: exps = vector(exp)*d[s]
    sage: product(U.gens()[i]^exps[i] for i in range(2))
    u0*u1^2

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

@cached_function(key=lambda s, K, e: (str(s), s.parent().number_field(), K))
def galois_field_extend(sigma, K, embedding=None):
    r"""Find the extension of a galois homomorphism to a bigger field.

    INPUT:

    - ``sigma`` -- A galois homomorphism on some field $K_0$

    - ``K`` -- A galois field extension of $K_0$

    - ``embedding`` -- An embedding of $K_0$ into `K`. By default will
      be the first embedding found by the method :meth:`embeddings`.

    OUTPUT:

    An element $\tau$ of the galois group of `K`, such that $\tau$
    restricted to $K_0$ is `sigma`.

    EXAMPLES::

    Simple example::

        sage: K = QuadraticField(2)
        sage: L = CyclotomicField(8)
        sage: sigma = K.galois_group().gen()
        sage: tau = galois_field_extend(sigma, L); tau
        (1,3)(2,4)
        sage: tau.parent()
        Galois group of Cyclotomic Field of order 8 and degree 4
        sage: galois_field_restrict(tau, K) == sigma
        True

    Note that the extension is not unique::

        sage: K = QuadraticField(2)
        sage: L = CyclotomicField(8)
        sage: tau = L.galois_group()[3]
        sage: sigma = galois_field_restrict(tau, K)
        sage: galois_field_extend(sigma, L) == tau
        False

    """
    Gsmall = sigma.parent()
    Ksmall = Gsmall.number_field()
    Gbig = K.galois_group()
    Kbig = Gbig.number_field()
    if Gsmall == Gbig and Ksmall == Kbig:
        return sigma
    if embedding is None:
        embedding = Ksmall.embeddings(Kbig)[0]
    for tau in Gbig:
        if tau(embedding(Ksmall.gen())) == embedding(sigma(Ksmall.gen())):
            return tau
    raise Exception("No corresponding galois action found for %s."%sigma)

@cached_function(key=lambda s, K, e: (str(s), s.parent().number_field(), K))
def galois_field_restrict(sigma, K, embedding=None):
    r"""Find the restriction of a galois homomorphism to a smaller field.

    INPUT:

    - ``sigma`` -- A galois homomorphism on some field $K_0$

    - ``K`` -- A galois subfield of $K_0$

    - ``embedding`` -- An embedding of K into K0. By default will be
      the first embedding found by the method :meth:`embeddings`.

    OUPUT:
    
    An element $\tau$ of the galois group of `K` such that `sigma` and
    $\tau$ act the same on elements of `K`.

    EXAMPLE::

        sage: K = QuadraticField(3)
        sage: L = CyclotomicField(24)
        sage: tau = L.galois_group().gens()[0]
        sage: sigma = galois_field_restrict(tau, K); sigma
        (1,2)
        sage: sigma.parent()
        Galois group of Number Field in a with defining polynomial x^2 - 3

    """
    Gsmall = K.galois_group()
    Ksmall = Gsmall.number_field()
    Gbig = sigma.parent()
    Kbig = Gbig.number_field()
    if Gbig == Gsmall and Ksmall == Kbig:
        return sigma
    if embedding is None:
        embedding = Ksmall.embeddings(Kbig)[0]
    for tau in Gsmall:
        if sigma(embedding(Ksmall.gen())) == embedding(tau(Ksmall.gen())):
            return tau
    raise Exception("No corresponding galois action found for %s."%tau)

@cached_function(key=lambda s, K: (str(s), s.parent().number_field(), K))
def galois_field_change(sigma, K):
    r"""Change a Galois homomorphism to one on a specified field
    
    Given a galois homomorphism $\sigma$ and a galois number field
    $K$, will find a galois homomorphism $\tau$ of $K$ such that
    $\sigma$ and $\tau$ have a common extension to a galois
    homomorphism of the algebraic closure of $\Q$.

    .. NOTE::

    The galois homomorphism returned by this method only agrees with
    the given galois homomorphism on the intersection of their
    respective number fields.

    INPUT:
    
    - ``sigma`` -- An element of the galois group of some number field
      $K_0$.

    - ``K`` -- A galois number field.

    OUTPUT:

    An element $\tau$ of the galois group of `K`, such that `sigma`
    and $\tau$ have a common extension to the compositum of $K_0$ and
    `K`, i.e. there is some galois homomorphism $\mu$ on $K_0 K$ that
    acts the same as `sigma` on $K_0$ and the same as $\tau$ on
    `K`.

    EXAMPLES:

    Can convert from a very complicated field to a very simple one::

        sage: K = QuadraticField(10)
        sage: L = CyclotomicField(120)
        sage: tau = L.galois_group()[5]; tau
        (1,6,3,8)(2,7,4,5)(9,14,11,16)(10,15,12,13)(17,22,19,24)(18,23,20,21)(25,30,27,32)(26,31,28,29)
        sage: sigma = galois_field_change(tau, K); sigma
        (1,2)
        sage: sigma.parent()
        Galois group of Number Field in a with defining polynomial x^2 - 10

    Can also be used on two totally unrelated fields, but the result
    can be totally unexpected::

        sage: K = QuadraticField(2)
        sage: L = QuadraticField(3)
        sage: sigma = K.galois_group().gen(); sigma
        (1,2)
        sage: tau = galois_field_change(sigma, L); tau
        ()
        sage: tau.parent()
        Galois group of Number Field in a with defining polynomial x^2 - 3

    """
    L = sigma.parent().number_field()
    M, L_to_M, K_to_M = composite_field(L, K, give_maps=True)
    return galois_field_restrict(galois_field_extend(sigma, M, embedding=L_to_M),
                                 K, embedding=K_to_M)

@cached_function(key=lambda s, N: ((0, s, N) if s in ZZ else
                                   (str(s), s.parent().number_field(), N)))
def cyclotomic_galois_isomorphism(s, N=None):
    r"""Realize the isomorphism between the galois group of a cyclotomic
    field and $\Z/N\Z^*$

    There is a natural isomorphism between the group $(\Z/N\Z)^*) and
    the galois group of $\Q(\zeta_N)$ where the integer $n$
    corresponds to the galois homomorphism $\zeta_N \mapsto
    \zeta_N^n$. This function allows one to convert the element of
    one of these groups into the other.

    INPUT:

    - ``s`` -- An integer with gcd(s,N) == 1 or an element of the
      galois group of a number field.

    - ``N`` -- A strictly positive integer indicating the order of the
      cyclotomic field. Should be specified if s is an
      integer. Otherwise defaults to the size of the torsion of the
      corresponding number field.
    
    OUTPUT:

    If `s` was an integer, will return an element $\sigma$ of the galois
    group of $\Q(\zeta_N)$ such that $ \sigma(\zeta_N) = \zeta_N^s $

    If `s` was an element of the galois group of a number field $K$,
    will return an integer `n` such that $s(\zeta) == \zeta^n$, where
    $\zeta$ is a generator of the roots of unity in $K$. If `N` was
    specified will do the same but will rather replace $K$ by the
    field $\Q(\zeta_N)$, replace `s` by a galois homomorphism of that
    $\Q(\zeta_N)$ that has a common extension with `s`, and replace
    $\zeta$ by $\zeta_N$.

    EXAMPLES:

    Converting from an integer to a galois homomorphism::

        sage: sigma = cyclotomic_galois_isomorphism(3, N=8); sigma
        (1,4)(2,3)
        sage: sigma.parent()
        Galois group of Cyclotomic Field of order 8 and degree 4

    Converting from a galois homomorphism to the corresponding
    integer::

        sage: L = CyclotomicField(30)
        sage: sigma = L.galois_group()[2]; sigma
        (1,3)(2,4)(5,7)(6,8)
        sage: cyclotomic_galois_isomorphism(sigma)
        19

    If the modulus is given can convert from a galois homomorphism
    over any field::

        sage: K = QuadraticField(5)
        sage: sigma = K.galois_group().gen()
        sage: cyclotomic_galois_isomorphism(sigma, N=5)
        2

    """
    if s in ZZ:
        if N is None:
            raise Exception("Need to specify N if s is an integer")
        L.<zeta> = CyclotomicField(N)
        G = L.galois_group()
        for sigma in G:
            if sigma(zeta) == zeta^s:
                return sigma
        raise Exception("No galois element corresponds to %s."%s)
    G = s.parent()
    L = G.number_field()
    if N is None:
        N = L.zeta_order()
    else:
        s = galois_field_change(s, CyclotomicField(N))
        G = s.parent()
        L = G.number_field()
    i = 0
    zeta = L.zeta(N)
    zeta_s = s(zeta)
    while zeta_s != 1:
        zeta_s = zeta_s/zeta
        i += 1
    return i

@cached_function
def galois_on_units(K):
    r"""Compute how the galois group of a field acts on its units.

    INPUT:

    - ``K`` -- A galois number field.
    
    OUTPUT:
    
    A dictionary indexed by the elements of the galois group of `K`,
    such that the value with key $\sigma$ is a matrix with integer
    coefficients. If $u_0$, ..., $u_n$ are the generators of the unit
    group of `K` as given by :meth:`unit_group` and $a_0$, ..., $a_n$
    are the entries of the i-th row of this matrix, then $u_i$ is
    mapped to $u_0^{a_0} * ... * u_n^{a_n} by s.

    EXAMPLE::

        sage: K = QuadraticField(3)
        sage: G.<s> = K.galois_group()
        sage: d = galois_on_units(K)
        sage: U(s(product(U.gens()[i]^exp[i] for i in range(2))))
        u0*u1^2
        sage: exps = vector(exp)*d[s]
        sage: product(U.gens()[i]^exps[i] for i in range(2))
        u0*u1^2

    """
    G = K.galois_group()
    U = K.unit_group()
    return {s : matrix([U(s(u)).list() for u in U.gens()]).transpose() for s in G}
