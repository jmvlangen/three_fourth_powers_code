r"""
Some code to solve a specific sort of linear problem.

Code to solve linear problems over the integers where some relations
might be defined modulo some positive integer.

EXAMPLES:

Let's find all pairs of integers that sum to 2018 and have the
same last digit, i.e. congruent modulo 10::

    sage: M = matrix([1,1]); M
    [1 1]
    sage: V = vector([2018]); V
    (2018)
    sage: MT = matrix([1,-1]); MT
    [ 1 -1]
    sage: VT = vector([0]); VT
    (0)
    sage: N = 10
    sage: solve_integer_problem_with_torsion(M, V, MT, VT, N, all=True)
    (
                [ 5]
    (-1, 2019), [-5]
    )

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

def solve_integer_problem_with_torsion(M, V, MT, VT, N, all=False):
    r"""Solve a linear problem over the integers with some relations
    modulo some N.

    This function solves linear problems of the form .. MATH::

        \begin{aligned}
        M x & = v \\
        M' x & \equiv v' \quad \text{(mod )} N \text{).}
        \end{aligned}

    Here $M$, $M'$ are matrixes with integer coefficients, $x$, $v$
    and $v'$ are row vectors with integer coefficients and $N$ is a
    positive integer.  We solve the problem for $x$.

    INPUT:

    - ``M`` -- An `m` by `n` matrix with integer coefficients.

    - ``V`` -- A vector of length `m` with integer coefficients.

    - ``MT`` -- An `mt` by `n` matrix with coefficients in the
      integers or the integers modulo N.

    - ``VT`` -- A vector of length `mt` with coefficients in the
      integers or the integers modulo N.

    - ``N`` -- A non-negative integer giving the modulus of the
      problem.

    - ``all`` -- A boolean indicating whether a single solution or all
      solutions to this problem should be returned.

    OUTPUT:
    
    A vector v of length `n` with integer coefficients such that M * v
    == V and MT * v == VT modulo N. If the parameter all is set to
    True, will return a tuple with as first entry such a vector v and
    as the second entry an n by n0 matrix A such that the map $y
    \mapsto v + A y$ maps n0 vectors with integer coefficients
    surjectively to the set of all solutions of the system.

    EXAMPLES:

    Let's find all pairs of integers that sum to 2018 and have the
    same last digit, i.e. congruent modulo 10::

        sage: M = matrix([1,1]); M
        [1 1]
        sage: V = vector([2018]); V
        (2018)
        sage: MT = matrix([1,-1]); MT
        [ 1 -1]
        sage: VT = vector([0]); VT
        (0)
        sage: N = 10
        sage: solve_integer_problem_with_torsion(M, V, MT, VT, N, all=True)
        (
                    [ 5]
        (-1, 2019), [-5]
        )

    """
    # Make sure the rings are right
    M = M.change_ring(ZZ)
    V = V.change_ring(ZZ)
    MT = MT.change_ring(Integers(N))
    VT = VT.change_ring(Integers(N))

    # Calculation + checking that a solution exists
    m, n = M.dimensions()
    mt, nt = MT.dimensions()
    M0 = block_matrix(2,2,[M, zero_matrix(m, mt), MT.change_ring(ZZ),
                           diagonal_matrix([N]*mt)])
    V0 = vector(list(V) + list(VT.change_ring(ZZ)))
    MV0 = block_matrix(1,2,[M0,V0.column()])
    B = MV0.right_kernel().basis_matrix().transpose()
    g = B[-1][0]
    c = [1]
    for i in range(1, len(B[-1])):
        g, s, t = xgcd(g,B[-1][i])
        for j in range(len(c)):
            c[j] = c[j] * s
        c.append(t)
    if abs(g) != 1:
        raise ArithmeticError("The system does not have a solution.")
    v0 = -g * B * vector(c)
    v = v0[:n]
    if all:
        A0 = M0.right_kernel().basis_matrix().transpose()
        A = A0[:n]
        return (v, A)
    else:
        return v
