r"""Functions to compute with cocycles and coboundaries in (galois)
group cohomology.

This file contains two main functions. The first allows one to
find the function whose coboundary is a given cocycle on a finite
group with values in a finitely generated abelian group. The second
allows one to explicitly compute the constant of which existence
is proven by Hilbert90.

EXAMPLES:

An example of computing the function with a given coboundary::

    sage: G = SymmetricGroup(3)
    sage: A = AbelianGroup(3)
    sage: action = {s : matrix([[(1 if s(j) == i else 0) for i in range(1,4)] for j in range(1,4)]) for s i
    ....: n G}
    sage: def alpha(s):
    ....:     return A([(s.order() if s(i) != i else 0) for i in range(1,4)])
    ....: 
    sage: def c(s, t):
    ....:     return A(vector(alpha(s).list()) + vector(alpha(t).list()) * action[s] - vector(alpha(s*t).li
    ....: st()))
    ....: 
    sage: alpha2 = function_with_coboundary(G, A, c, action=action)
    sage: [alpha(s) for s in G]
    [1, f0^2*f1^2, f0^3*f1^3*f2^3, f0^3*f1^3*f2^3, f1^2*f2^2, f0^2*f2^2]
    sage: [alpha2(s) for s in G]
    [1, f0^2*f1^2, f0^3*f1^3*f2^3, f0^3*f1^3*f2^3, f1^2*f2^2, f0^2*f2^2]

We do an explicit computation of Hilbert90::

    sage: K.<a> = QuadraticField(3)
    sage: G = K.galois_group()
    sage: def f(s):
    ....:     if s == G[0]:
    ....:         return 1
    ....:     else:
    ....:         return a + 2
    ....:     
    sage: b = hilbert90(K, f); b
    -a + 3
    sage: [s(b) / b for s in G]
    [1, a + 2]

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

from sage.rings.number_field.number_field import is_NumberField

def _independent_cocycle_arguments(G):
    r"""Give a list of arguments for a 2-cocycle that uniquely determines
    it.

    A 2-cocycle $c : G^2 \to A$ satisfies for any $s$, $t$ and $u$ in
    G ..MATH ::

        s(c(t, u)) - c(s*t, u) + c(s, t*u) - c(s, t) = 0

    These give us the equations ..MATH ::
    
        \begin{aligned}
        c(1, s) = c(1, 1) \quad & \text{for all} s \neq 1, \\
        c(s, 1) = s(c(1, 1)) \quad & \text{for all} s \neq 1, \\
        c(s^2, s) = s(c(s, s)) + c(s, s^2) - c(s, s) \quad
        & \text{for all} s \neq 1, \\
        c(s, t) = s(c(t, u)) - c(s*t, u) + c(s, t*u) \quad
        & \text{for all} s, t, u \in G \setminus \{1\} \text{ not all the same}\\
        \end{aligned}

    Starting with a list of all pairs of elements of G, as long as
    all the pairs appearing in one of these equations appear in the
    list, we remove the pair appearing before the equality sign from
    the list.
    
    INPUT:

    - ``G`` -- A finite group

    OUTPUT:

    A list of pairs of elements of G, such that knowing the value of a
    2-cocycle at these pairs uniquely determines the 2-cocycle.  This
    list is minimal in the sense that no sublist has the same
    property.

    """
    result = [(s, t) for s in G for t in G]
    G_without_1 = [s for s in G if s != G.identity()]
    for s in G_without_1:
        if (G.identity(), s) in result:
            result.remove((G.identity(), s)) # (1, 1) is always in the list
        if (s, G.identity()) in result:
            result.remove((s, G.identity())) # (1, 1) is always in the list
        if (s^2, s) in result and (s, s^2) in result and (s, s) in result:
            result.remove((s^2, s)) 
        for t in G_without_1:
            if (s, t) in result:
                for u in G_without_1:
                    if (not (s == t and t == u) and (t, u) in result and
                        (s*t, u) in result and (s, t*u) in result):
                        result.remove((s, t))
                        break
    return result

def function_with_coboundary(G, A, c, action=None):
    r"""Give a function G -> A with coboundary c.

    INPUT:

    - ``G`` -- A finite group

    - ``A`` -- An abelian group with an action of G defined on
      it. This may be given as a Sage implementation of a
      multiplicative abelian group or as a tuple containing in this
      order: the identity of A; a list of generators of A; a list of
      the corresponding orders; and a function that converts an
      element of A into a list of exponents such that the product of
      each generator to its respective exponent is the given element.

    - ``c`` -- A coboundary of G with values in A, given as a function
      with two arguments that returns a value in A, i.e. for s and t
      in G the operation c(s,t) should be defined and give an element
      of A.

    - ``action`` -- An optional dictionary (default: None) providing
      the action of G on A. Each element of G should be a key in this
      dictionary and the corresponding value should be a matrix such
      that the i,j-th entry is the exponent of the j-th generator in
      the image of the action on the i-th generator of A for this
      elment of G.  If set to None will use s(u) to determine these
      matrices for each s in G and u in A

    OUTPUT:

    A function a that given an element of G will return an element of
    A and satisfies: a(s) + s(a(t)) - a(s*t) == c(s,t) for all s and t
    in G, where * and + are the group operations on G and A
    respectively and s(a(t)) is the element s of G acting on the
    element a(t) of A.

    EXAMPLES:

    A typical example is the case where we have the galois group of a
    field act on the group of units::

        sage: K = QuadraticField(3)
        sage: U = K.unit_group()
        sage: G = K.galois_group()
        sage: def c(s, t):
        ....:     if s == G.identity():
        ....:         return U.gens()[1]
        ....:     else:
        ....:         return U.gens()[1]^(-1)
        ....:     
        sage: alpha = function_with_coboundary(G, U, c)
        sage: [alpha(s) for s in G]
        [u1, 1]
        sage: matrix([[K(alpha(s) * U(s(alpha(t))) * alpha(s*t)^(-1)) for t in G] for s in G])
        [ a - 2  a - 2]
        [-a - 2 -a - 2]
        sage: matrix([[K(c(s,t)) for t in G] for s in G])
        [ a - 2  a - 2]
        [-a - 2 -a - 2]

    An example in which we obtain back the function from which the
    coboundary was constructed::

        sage: G = SymmetricGroup(3)
        sage: A = AbelianGroup(3)
        sage: action = {s : matrix([[(1 if s(j) == i else 0) for i in range(1,4)] for j in range(1,4)]) for s i
        ....: n G}
        sage: def alpha(s):
        ....:     return A([(s.order() if s(i) != i else 0) for i in range(1,4)])
        ....: 
        sage: def c(s, t):
        ....:     return A(vector(alpha(s).list()) + vector(alpha(t).list()) * action[s] - vector(alpha(s*t).li
        ....: st()))
        ....: 
        sage: alpha2 = function_with_coboundary(G, A, c, action=action)
        sage: [alpha(s) for s in G]
        [1, f0^2*f1^2, f0^3*f1^3*f2^3, f0^3*f1^3*f2^3, f1^2*f2^2, f0^2*f2^2]
        sage: [alpha2(s) for s in G]
        [1, f0^2*f1^2, f0^3*f1^3*f2^3, f0^3*f1^3*f2^3, f1^2*f2^2, f0^2*f2^2]

    """
    if isinstance(A, tuple):
        identity, gens, orders, convert = A
    else:
        identity = A.identity()
        gens = A.gens()
        orders = [a.order() for a in gens]
        def convert(u):
            return A(u).list()
    if action is None:
        action = {s : [convert(s(u)) for u in gens] for s in G}
    action = {s : matrix(action[s]).transpose() for s in action}

    # The variables
    m = len(G.gens()) # Number of generators of G
    n = len(gens) # Number of generators of A
    alpha0 = {G.gens()[i]: block_matrix(1, m+1,
                                        [(identity_matrix(n) if j == i
                                          else zero_matrix(n))
                                         for j in range(m)] +
                                        [vector([0]*n).column()])
              for i in range(m)}
    def c_to_matrix(s,t):
        return block_matrix([[zero_matrix(n) for j in range(m)] +
                             [vector(convert(c(s, t))).column()]])
    relations = _independent_cocycle_arguments(G)
    # We always have alpha(1) = c(1, 1)
    alpha0[G.identity()] = c_to_matrix(G.identity(), G.identity())
    relations.remove((G.identity(), G.identity()))
    while len(alpha0) < len(G):
        keys = alpha0.keys()
        for s in keys:
            for t in keys:
                if s*t not in alpha0:
                    alpha0[s*t] = (alpha0[s] + (action[s] * alpha0[t])
                                   - c_to_matrix(s, t))
                    if (s,t) in relations:
                        relations.remove((s,t))

    # Building a matrix:
    MV = block_matrix(len(relations), 1, [alpha0[s] + action[s]*alpha0[t]
                                          - alpha0[s*t] - c_to_matrix(s, t)
                                         for (s, t) in relations])

    # Changing torsion to one modulus
    tor_gens = [k for k in range(n) if orders[k] in ZZ]
    N = lcm(orders[k] for k in tor_gens)
    for k in tor_gens:
        if orders[k] < N:
            g = ZZ(N / orders[k])
            for i in range(len(relations)):
                MV.rescale_row(i*n + k, g)

    # Seperating torsion
    tor_rows = [i*n + k for i in range(len(relations)) for k in tor_gens]
    MVF = MV.delete_rows(tor_rows)
    MVT = MV.matrix_from_rows(tor_rows)

    # Extracting the distinct matrices
    MF = MVF[:,:-1]
    VF = -MVF[:,-1]
    if VF.dimensions()[0] == 0:
        VF = vector([])
    else:
        VF = vector(VF)
    MT = MVT[:,:-1]
    VT = -MVT[:,-1]
    if VT.dimensions()[0] == 0:
        VT = vector([])
    else:
        VT = vector(VT)

    # Solving and giving the result
    v = solve_integer_problem_with_torsion(MF, VF, MT, VT, N)
    @cached_function
    def alpha(s):
        result = identity
        val = alpha0[s] * block_matrix(2,1,[v.column(), identity_matrix(1)])
        for k in range(n):
            result = result * gens[k]^val[k][0]
        return result
    return alpha

def hilbert90(K, f):
    r"""Compute an element that proves Hilbert 90 for a given function.

    Let K be a galois number field and f be a function from the galois
    group of K to the non-zero elements of K. If for any s,t in that
    galois group f satisfies f(s) * s(f(t)) == f(s*t), then by Hilbert
    90 there exists a non-zero element a of K such that for any s in
    the galois group we have f(s) = s(a)/a

    INPUT:

    - ``K`` -- A galois number field.

    - ``f`` -- A function from the galois group of K to the non-zero
      elements of K, such that for any two automorphisms s and t of K
      we have f(s) * s(f(t)) == f(s*t).

    OUTPUT:
    
    A non-zero element a of K such that for any automorphism s of K we
    have s(a) = f(s)*a.  Furthermore this element has the minimal
    integral norm among such elements.

    EXAMPLE::

        sage: K.<a> = QuadraticField(3)
        sage: G = K.galois_group()
        sage: def f(s):
        ....:     if s == G[0]:
        ....:         return 1
        ....:     else:
        ....:         return a + 2
        ....:     
        sage: b = hilbert90(K, f); b
        -a + 3
        sage: [s(b) / b for s in G]
        [1, a + 2]

    """
    if not (is_NumberField(K) and K.is_galois()):
        raise ValueError("%s is not a galois number field."%(K,))
    while K.base() != QQ:
        K = K.absolute_field(names=[str(g) for g in K.gens()])
    G = K.galois_group()
    if not all(f(s) * s(f(t)) == f(s*t) for s in G for t in G):
        raise ValueError("%s is not a valid function for Hilbert 90."%(f,))
    for b in K.power_basis():
        a = sum(s(b)/K(f(s)) for s in G)
        if a != 0:
            break
    else:
        raise ArithmeticError("Disproved Hilbert 90")
    # We compute the biggest rational n such that a is an integral
    # element times n
    I = a.numerator_ideal()
    J = a.denominator_ideal()
    d = I.smallest_integer()
    m = (K.ideal(d)*J*I^(-1)).smallest_integer()    
    n = d / m
    return a / n
