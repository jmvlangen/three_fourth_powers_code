r"""Code for using dirichlet characters as galois characters.

Since the galois group of the cyclotomicfield $\Q(\zeta_N)$ is
naturally isomorphic to $(\Z / N\Z)^*$ there is a natural
correspondence between galois characters of such fields and Dirichlet
characters. By the Kronecker-Weber theorem this can be exended to all
abelian extension of $\Q$.

This file provides methods to work with Dirichlet characters as galois
characters. For example there is a method to convert them into galois
characters, a method to compute the fixed field of their kernel as a
galois character and there is a method to compute the quadratic
Dirichlet character corresponding to the quadratic galois character of
a quadratic field.

EXAMPLES:

We can interpret a Dirichlet character as a galois character over the
fixed field of its kernel::

    sage: eps = DirichletGroup(24)[5]; eps
    Dirichlet character modulo 24 of conductor 12 mapping 7 |--> -1, 13 |--> 1, 17 |--> -1
    sage: K = dirichlet_fixed_field(eps); K
    Number Field in zeta0 with defining polynomial x^2 - 3
    sage: G = K.galois_group()
    sage: eps_gal = dirichlet_to_galois(eps)
    sage: [eps_gal(s) for s in G]
    [1, -1]

Conversely we can find the dirichlet character corresponding to a
quadratic galois character::

    sage: eps = character_for_root(-5); eps
    Dirichlet character modulo 20 of conductor 20 mapping 11 |--> -1, 17 |--> -1
    sage: dirichlet_fixed_field(eps)
    Number Field in zeta0 with defining polynomial x^2 + 5

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

def dirichlet_fixed_field(eps):
    r"""Give the fixed field of the kernel of a Dirichlet chracter.

    INPUT:
    
    - ``eps`` -- A Dirichlet character.

    OUTPUT:
    
    A subfield $K$ of $\Q(\zeta_N)$ where $N$ is the conductor of eps.
    For each $n$ in the kernel of eps, $K$ is invariant under the map
    $ \zeta_N \mapsto \zeta_N^n $.

    EXAMPLES:

    Generators of the Dirichlet group of modulus 8 have quadratic
    fixed fields::

        sage: D = DirichletGroup(8)
        sage: for eps in D.gens():
        ....:     print dirichlet_fixed_field(eps)
        ....:     
        Cyclotomic Field of order 4 and degree 2
        Number Field in zeta0 with defining polynomial x^2 - 2

    The trivial character has the rational field as its fixed field::

        sage: eps = DirichletGroup(5)[0]; eps
        Dirichlet character modulo 5 of conductor 1 mapping 2 |--> 1
        sage: dirichlet_fixed_field(eps)
        Rational Field
    
    A primitive character with a prime modulus has the entire
    cyclotomic field as a fixed field::
    
        sage: eps = DirichletGroup(7).gen(); eps
        Dirichlet character modulo 7 of conductor 7 mapping 3 |--> zeta6
        sage: dirichlet_fixed_field(eps)
        Cyclotomic Field of order 7 and degree 6

    """
    eps = eps.primitive_character()
    N = eps.conductor()
    return fixed_field([cyclotomic_galois_isomorphism(s, N) for s in eps.kernel()])
    # H = [cyclotomic_galois_isomorphism(s, N) for s in eps.kernel()]
    # G = CyclotomicField(N).galois_group()
    # H = G.subgroup(H)
    # if H == G:
    #     return QQ
    # result = H.fixed_field()
    # if isinstance(result, tuple):
    #     return result[0]
    # else:
    #     return result

def dirichlet_to_galois(eps):
    r"""Give the galois character associated to a Dirichlet character.

    INPUT:
    
    - ``eps`` -- A Dirichlet character $\varepsilon$.

    OUTPUT:
    
    A function $f$ that is the galois version of the Dirichlet character
    $\varepsilon$, e.g. we have ..MATH:
    
        f( \zeta_N \mapsto \zeta_N^n ) = \varepsilon(n)

    where $N$ is any number divisible by the conductor of
    $\varepsilon$. This function takes any element of a galois group
    of a number field and returns the appropiate value on a galois
    homomorphism of $\Q(\zeta_N)$ that has a common extension to the
    absolute galois group of~$\Q$.

    EXAMPLE::
    
        sage: eps = DirichletGroup(5).gen(); eps
        Dirichlet character modulo 5 of conductor 5 mapping 2 |--> zeta4
        sage: eps_gal = dirichlet_to_galois(eps)
        sage: for g in CyclotomicField(5).galois_group():
        ....:     print eps_gal(g)
        ....:     
        1
        zeta4
        -1
        -zeta4

    """
    eps = eps.primitive_character()
    N = eps.conductor()
    def eps_galois(sigma):
        return eps(cyclotomic_galois_isomorphism(sigma, N=N))
    return eps_galois

def character_for_root(a):
    r"""Give the Kronecker character of a given number.

    INPUT:

    - ``a`` -- A non-zero integer.

    OUTPUT:

    A Dirichlet character eps such that the associated galois
    character has fixed field $ \Q(\sqrt{a}) $

    EXAMPLES::

        sage: eps = character_for_root(-3); eps
        Dirichlet character modulo 3 of conductor 3 mapping 2 |--> -1
        sage: K = dirichlet_fixed_field(eps); K
        Cyclotomic Field of order 3 and degree 2
        sage: K(-3).is_square()
        True

    ::

        sage: eps = character_for_root(6); eps
        Dirichlet character modulo 24 of conductor 24 mapping 7 |--> -1, 13 |--> -1, 17 |--> -1
        sage: K = dirichlet_fixed_field(eps); K
        Number Field in zeta0 with defining polynomial x^2 - 6

    .. SEEALSO::

        :func:`dirichlet_fixed_field`

    """
    a = a.squarefree_part()
    ls = a.prime_factors()
    ls.append(a.sign())
    N = 1
    eps = DirichletGroup(1)[0]
    for i in range(len(ls)-1):
        m = mod(ls[i],4)
        if m != 2:
            D = DirichletGroup(ls[i])
        if m == 1:
            N *= ls[i]
            eps = eps.extend(N) * (D.gen()^ZZ(D.order()/2)).extend(N)
        elif m == 2:
            N *= 8
            eps = eps.extend(N) * _character_for_2(2).extend(N)
        elif m == 3:
            N *= ls[i]
            ls[-1] *= -1
            eps = eps.extend(N) * (D.gen()^ZZ(D.order()/2)).extend(N)
        else:
            raise Exception("Invalid prime factor %s"%ls[i])
    if ls[-1] == -1:
        if not 4.divides(N):
            N *= 4
        D = DirichletGroup(4)
        eps = eps.extend(N) * D.gen().extend(N)
    return eps

def _character_for_2(a):
    r"""Give the Kronecker character of some numbers that have to do with
    2.

    INPUT:

    - ``a`` -- An integer from the list [-1, 2, -2]

    OUTPUT:

    A Dirichlet character eps such that the associated galois
    character has fixed field $ \Q(\sqrt{a}) $

    """
    D = DirichletGroup(8)
    if a == -1:
        b = 5
    elif a == 2:
        b = 7
    elif a == -2:
        b = 3
    else:
        raise Exception("Value %s not accepted"%a)
    for eps in D:
        if len(eps.kernel()) == 2 and b in eps.kernel():
            return eps
    raise Exception("No character found!")
