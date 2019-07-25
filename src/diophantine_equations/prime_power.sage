r"""Classes to work with diophantine equations containing a prime
power.

Given a diophantine equation of the form .. MATH::

    f(x_1, \ldots, x_n) = y^l

with $f$ some polynomial, one can show some results about integer
solutions $x_1, \ldots, x_n, y, l$ with $l$ prime. This file adds a
class that automates some of the reasoning done for this.

EXAMPLES:

TODO

AUTHORS:

- Joey van Langen (2019-03-07): initial version

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
from sage.combinat.combination import Combinations

class power_analyzer(SageObject):
    r"""A class used to analyze diophantine equations containing a prime
    power.

    A class providing useful methods to analyze the solutions of a
    diophantine equation of the form .. MATH::

       f(x_1, \ldots x_n) = y^l

    where $f$ is a polynomial over the rationals. Here we are
    interestend in solutions $x_1, \ldots, x_n, y, l \in \Z$ with $l$
    prime.
    
    Throughout the documentation of this class we will use the
    notation above to describe what methods do.

    """

    def __init__(self, f):
        r"""Initialize this power analyzer
        
        INPUT:

        - ``f`` -- The polynomial $f$ defined over the rationals.

        """
        self._f = f

    def factor(self, K):
        r"""Give a factor of the polynomial $f$ over the field `K`

        INPUT:

        - ``K`` -- An extension of the field over which $f$ is
          defined.

        OUTPUT:

        A factor of the polynomial $f$ over the given field K.

        """
        return self._f.change_ring(K).factor()[0][0]

    def coprimality(self, K, g=None):
        r"""Determine which factors of $f$ are coprime.

        INPUT:

        - ``K`` -- A galois extension of the field over which $f$ is
          defined.

        - ``g`` -- A factor of the polynomial $f$ defined over the
          field `K`. By default will be the outcome of :meth:`factor`

        OUTPUT:
        
        A dictionary indexed by elements of the galois group of `K`,
        such that the entry with key $\sigma$ has a value that is
        divisible by all primes that divide both `g` and the $\sigma$
        conjugate of `g`.
        
        .. NOTE::

        The values that come from this method might be polynomials
        themselves as the specific primes might depend on the values
        of the polynomial. This is a specific number if $f$ has only
        one variable or if $f$ is homogenous in two variables, in
        which case the variables are assumed to be coprime.

        """
        if g is None:
            g = self.factor(K)
        if g.is_homogeneous():
            return {s : g.macaulay_resultant(g.change_ring(s.as_hom()))
                    for s in K.galois_group()}
        else:
            return {s : g.resultant(g.change_ring(s.as_hom()))
                    for s in K.galois_group()}

    def relations(self, K, g=None):
        r"""Give possible relations between $f$ and a factor.
        
        If $g$ is a factor of $f$ over some galois field extension,
        multiplying certain galois conjugates of $g$ will result in a
        constant times the polynomial. A relation is a combination of
        the required galois homomorphisms and the corresponding
        coefficient.

        INPUT:

        - ``K`` -- A galois extension of the field over which $f$ is
          defined.

        - ``g`` -- A factor of the polynomial $f$ defined over the
          field `K`. By default will be the outcome of :meth:`factor`

        OUTPUT:

        A list of tuples of the form $(\sigma_1, ..., \sigma_n, c)$
        with $\sigma_1, ..., \sigma_n$ elements of the galois group of
        `K` and $c$ an element of `K`, such that the product of `g`
        conjugated by each $\sigma_i$ is equal to $c$ times the
        polynomial $f$.

        """
        if g is None:
            g = self.factor(K)
        n = ZZ(self._f.degree() / g.degree())
        G = K.galois_group()
        G_ls = [s for s in G if s != G(1)]
        result = []
        for s_ls in Combinations(G_ls, n - 1):
            candidate = g * product(g.change_ring(s.as_hom()) for s in s_ls)
            test = (candidate / self._f)
            if test.denominator() == 1:
                # We found a relation
                result.append(([G(1)] + list(s_ls),
                               K(test.numerator().constant_coefficient())))
        return result

    @cached_method
    def bad_primes(self, K, g=None):
        r"""Give the primes a factor $g$ of $f$ might not be an l-th power.

        INPUT:

        - ``K`` -- A galois extension of the field over which $f$ is
          defined.

        - ``g`` -- A factor of the polynomial $f$ defined over the
          field `K`. By default will be the outcome of :meth:`factor`

        OUTPUT:

        A list of all primes $P$ of `K` such that the order of $P$ in
        `g` is not necessarily a multiple of l when evaluated at a
        solution to the diophantine equation.

        """
        if g is None:
            g = self.factor(K)
        coprime = self.coprimality(K, g)
        result = reduce(lambda I, J: I + J,
                        [reduce(lambda I, J: I.intersection(J),
                                [K.ideal(coprime[t*s^(-1)])
                                 for s, t in Combinations(s_ls, 2)],
                                K.ideal(C))
                         for s_ls, C in self.relations(K, g)])
        if result == K.ideal(0):
            return 0
        else:
            return result.prime_factors()

    @cached_method
    def constant_coeff(self, K, g, bad_primes_val, l):
        r"""Give a constant $c$ such that a factor $g$ of $f$ is an $l$-th
        power times $c$.

        INPUT:

        - ``K`` -- A galois extension of the field over which $f$ is
          defined.

        - ``g`` -- A factor of the polynomial $f$ defined over the
          field `K`. By default will be the outcome of :meth:`factor`

        - ``bad_primes_val`` -- A tuple of integers, where each
          integer is the valuation of $g$ at the corresponding prime
          in the list returned by :meth:`bad_primes`.

        - ``l`` -- A strictly positive integer.

        OUTPUT:

        An element $c$ of `K` such that we have ..MATH::

          g = c u x^l

        for some $x$ in `K` and some unit $u$ in the ring of integers
        of `K`. Here `g` is evaluated at a solution to the diophantine
        equation.

        """
        bad_primes = self.bad_primes(K, g)
        I = product(bad_primes[i]^bad_primes_val[i] for i in range(len(bad_primes)))
        C = K.class_group()
        I_exp = C(I).list()
        # We find the class CJ such that I = CJ^l
        CJ = C(1)
        for i in range(len(C.gens())):
            g, x, y = xgcd(l, C.gens()[i].order())
            CJ = CJ * C.gens()[i]^(ZZ(I_exp[i] * x / g))
        J = (CJ^(-1)).ideal()
        return (I * (J^l)).gens_reduced()[0]
    
    def unit_relation(self, K, g, c, relation, l):
        r"""Determine the relations on units defined by a relation on a factor
        of $f$.

        Given a factor $g$ of the polynomial $f$ over some galois
        extension $K$ of the field over which $f$ is defined, we can
        find relations between $g$ and $f$ as given :meth:`relations`.
        If we know that .. MATH::

          g = c u x^l

        for some $c, x \in K$ and unit $u$ in the ring of integers of
        $K$ and we express $u$ as $u = u_0^{y_0} \cdots u_n^{y_n}$ for
        some generators $u_0, \ldots, u_n$ of the unit group of `K`,
        then such a relation defines relations on the exponents $y_0,
        \ldots, y_n$. This method computes those relations.

        INPUT:

        - ``K`` -- A galois field extension of the field over which
          $f$ is defined.

        - ``g`` -- A factor of the polynomial $f$ over the field `K`.

        - ``c`` -- An element of `K`, such that $g = c u x^l$
          for some $x$ in `K` and some unit $u$ of the ring of
          integers of `K`

        - ``relation`` -- A tuple of the form $(\sigma_1, \ldots,
          \sigma_n, c)$ with $\sigma_1, \ldots, \sigma_n$ elements of
          the galois group of `K` and $c$ an element of `K`, such that
          the product over of the $\sigma_i$ of $g$ conjugated by that
          $\sigma_i$ is equal to $c$ times the polynomial $f$.

        - ``l`` -- A prime number, the exponent to be considered in
          the diophantine equation.

        OUTPUT:

        A tuple consisting of a matrix $M$ and a vector $v$ with
        integer coefficients. These are such that the vectors $y$
        satisfying $M y = v$ are precisely the exponents $y = (y_0,
        \ldots, y_n)$ such that the unit $u = u_0^{y_0} \cdots
        u_n^{y_n}$ in $g = c u x^l$ satisfies the given relation on
        `g`. Here $u_0, \ldots, u_n$ are the generators of the unit
        group of `K` as returned by :meth:`gens`.

        """
        s_ls, C = relation
        constant = C / product(s(c) for s in s_ls)
        l_part = product(P^(ZZ(e/l)) for P, e in K.ideal(constant).factor())
        l_part = l_part.gens_reduced()[0]
        U = K.unit_group()
        v = vector(U(constant / (l_part^l)).list()).column()
        galois_action = galois_on_units(K)
        M = sum(galois_action[s] for s in s_ls)
        relevant_units = [i for i in range(len(U.gens()))
                          if (U.gens()[i].order() == Infinity or
                              l.divides(U.gens()[i].order()))]
        M = copy(M[relevant_units])
        v = copy(v[relevant_units])
        return M, v

    @cached_method
    def unit_coeffs(self, K, g, l, c=None, bad_primes_val=None):
        r"""Determine the exponents of units for a factor of $f$.

        Given a factor $g$ of $f$ over some galois field extension $K$
        such that .. MATH::

            g = c u x^l

        for some $c, x \in K$ and unit $u$ in the ring of integers of
        $K$, we can write $u$ as $u = u_0^{y_0} \cdots u_n^{y_n}$ for
        some generators $u_0, \ldots, u_n$ of the unit group of
        $K$. This method computes the possible exponents $y_0, \ldots,
        y_n$.

        INPUT:

        - ``K`` -- A galois field extension of the field over which
          $f$ is defined.

        - ``g`` -- A factor of the polynomial $f$ over the field `K`.

        - ``l`` -- A prime number, the exponent to be considered in
          the diophantine equation.

        - ``c`` -- An element of `K` or None (default: None). This
          element must be such that $g = c u x^l$ for some $x$ in `K`
          and some unit $u$ of the ring of integers of `K`. If set to
          None will be initialized with the method
          :meth:`constant_coeff`.

        - ``bad_primes_val`` -- A tuple of integers, where each
          integer is the valuation of $g$ at the corresponding prime
          in the list returned by :meth:`bad_primes`. This argument
          only has to be provided if `c` is not given.

        OUTPUT:
        
        A list of tuples of integers modulo `l`, consisting of all
        those tuples $(y_0, \ldots, y_n)$ such that the unit $u =
        u_0^{y_0} \cdots u_n^{y_n}$ can satisfy $g = c * u * x^l$ for
        some $x$ in `K` whilst agreeing with all relations on `g`
        given by :meth:`relations`. Here $u_0, \ldots, u_n$ are the
        generators of the unit group of `K` as returned by
        :meth:`gens`.

        """
        if c is None:
            if bad_primes_val is None:
                raise ValueError("Must provide the argument 'bad_primes_val' "+
                                 "if the argument 'c' is not provided.")
            c = self.constant_coeff(K, g, bad_primes_val, l)
        relations = self.relations(K, g)
        n = len(relations)
        lin_rel = [self.unit_relation(K, g, c, rel, l) for rel in relations]
        M, v = [block_matrix(n, 1, Mi) for Mi in zip(*lin_rel)]
        sol0 = M.change_ring(Integers(l)).solve_right(v)
        ker = M.change_ring(Integers(l)).right_kernel()
        V = ker.ambient_module()
        sol0 = V(vector(sol0))
        result = [sol0 + V(vi) for vi in ker]
        for vi in result:
            vi.set_immutable()
        return result

    def units(self, K, g, l, c=None, bad_primes_val=None):
        r"""Determine the units for a factor of $f$.

        Given a factor $g$ of $f$ over some galois field extension $K$
        such that .. MATH::

            g = c u x^l

        for some $c, x \in K$ and unit $u$ in the ring of integers of
        $K$, finds all possible values of $u$ modulo $l$-th powers.

        INPUT:

        - ``K`` -- A galois field extension of the field over which
          $f$ is defined.

        - ``g`` -- A factor of the polynomial $f$ over the field `K`.

        - ``l`` -- A prime number, the exponent to be considered in
          the diophantine equation.

        - ``c`` -- An element of `K` or None (default: None). This
          element must be such that $g = c u x^l$ for some $x$ in `K`
          and some unit $u$ of the ring of integers of `K`. If set to
          None will be initialized with the method
          :meth:`constant_coeff`.

        - ``bad_primes_val`` -- A tuple of integers, where each
          integer is the valuation of $g$ at the corresponding prime
          in the list returned by :meth:`bad_primes`. This argument
          only has to be provided if `c` is not given.

        OUTPUT:
        
        A list of units of the ring of integers of `K` consisting of
        representatives of all units $u$ modulo $l$-th powers such
        that .. MATH::

           g = c u x^l

        for some $x$ in `K`.

        """
        coeffs = self.unit_coeffs(K, g, l, c=c, bad_primes_val=bad_primes_val)
        U = K.unit_group()
        return [product(U.gens()[i]^ZZ(cf[i])
                        for i in range(len(U.gens()))) for cf in coeffs]

    def prime_data(self, K, g, l, primes, c=None, bad_primes_val=None):
        r"""Compute the possible values of solutions modulo some primes.

        Given a factor $g$ of the polynomial $f$ over some galois
        field extension $K$ such that we have .. MATH::

           g = c u x^l

        for some $c, x \in K$ and unit $u$ in the ring of integers of
        $K$, one can consider this equation modulo all finite primes
        $P$ of $K$. Doing this for all primes above a prime number $p$
        gives us a limited set of values for solutions of the
        diophantine equation modulo $p$. This method computes these
        values for multiple prime numbers $p$.

        The units chosen in the equation for $g$ are obtained with the
        method :meth:`unit_coeffs` and the computation mentioned above
        is done for each possible unit separately. If for some prime
        number there is no possible values for a solution for a given
        unit, then this unit is omitted for all primes. This makes it
        run this method for multiple primes even if one is only
        interested in the result for a single prime.

        .. NOTE:

        For each prime $P$ of $K$ for which the residue field does not
        have a primitive $l$-th root of unity, the computation of
        possible values does not yield any restrictions. The
        computation is therefore limited to those prime numbers $p$
        for which there is a prime $P$ of $K$ above them for which the
        residue field does have a primitive $l$-th root of unity.

        INPUT:

        - ``K`` -- A galois field extension of the field over which
          $f$ is defined.

        - ``g`` -- A factor of the polynomial $f$ over the field `K`.

        - ``l`` -- A prime number, the exponent to be considered in
          the diophantine equation.

        - ``primes`` -- A list of prime numbers for which the possible
          values modulo that prime should be determined. It can also
          be set to a non-negative integer in which case this list
          will be initialized as all the prime numbers smaller than
          that number.

        - ``c`` -- An element of `K` or None (default: None). This
          element must be such that $g = c u x^l$ for some $x$ in `K`
          and some unit $u$ of the ring of integers of `K`. If set to
          None will be initialized with the method
          :meth:`constant_coeff`.

        - ``bad_primes_val`` -- A tuple of integers, where each
          integer is the valuation of $g$ at the corresponding prime
          in the list returned by :meth:`bad_primes`. This argument
          only has to be provided if `c` is not given.

        OUTPUT:
        
        A dictionary indexed by those prime numbers $p$ in the given
        list of primes for which the number of elements of a residue
        field of a prime above $p$ in `K` is 1 modulo `l`. For each
        prime number $p$ the corresponding value is a dictionary
        indexed by possible units $u$ modulo $l$-th powers such that
        $g = c u x^l$ for some $x$ in `K`. For each such $u$ the
        corresponding value is a list of tuples containing the
        possible values of the variables of $f$ for which the above
        relation is satisfied modulo all primes above $p$ in `K`.

        """
        if primes in ZZ:
            primes = prime_range(primes)
        if c is None:
            if bad_primes_val is None:
                raise ValueError("Must provide the argument 'bad_primes_val' "+
                                 "if the argument 'c' is not provided.")
            c = self.constant_coeff(K, g, bad_primes_val, l)
        u_dict = {cf : {} for cf in self.unit_coeffs(K, g, l, c=c)}
        U = K.unit_group()
        G = K.galois_group()
        n = len(g.variables())
        for p in primes:
            P = K.prime_above(p)
            if P in self.bad_primes(K, g):
                continue
            Fp = P.residue_field()
            if mod(len(Fp), l) != 1:
                continue
            xp = Fp.primitive_element()
            B = diagonal_matrix([Fp(u).log(xp) for u in U.gens()])
            done_cases = {}
            removed = []
            for cf in u_dict:
                case = B*cf
                case.set_immutable()
                if case in done_cases:
                    done_cf = done_cases[case]
                    if done_cf in removed:
                        removed.append(cf)
                    else:
                        u_dict[cf][p] = u_dict[done_cases[case]][p]
                else:
                    u = product(U.gens()[i]^ZZ(cf[i]) for i in range(len(cf)))
                    xgl = g*(c*u)^(-1)
                    xgl_poly = [xgl.change_ring(s.as_hom()).change_ring(Fp)
                                for s in G]
                    arg_ls = tuple(tuple(arg) for arg in mrange([p]*n)
                                   if gcd(arg) != 0 and
                                   all(xgl_arg == 0 or
                                       l.divides(xgl_arg.log(xp))
                                       for xgl_arg
                                       in (xgl(arg) for xgl in xgl_poly)))
                    if len(arg_ls) == 0:
                        removed.append(cf)
                    else:
                        u_dict[cf][p] = arg_ls
                    done_cases[case] = cf
            for cf in removed:
                del u_dict[cf]
        if len(u_dict) == 0:
            return {}
        primes = u_dict[u_dict.keys()[0]].keys()
        return {p : {product(U.gens()[i]^ZZ(cf[i]) for i in range(len(cf))) :
                     u_dict[cf][p] for cf in u_dict}
                for p in primes}

    def prime_conditions(self, K, g, l, primes, c=None, bad_primes_val=None):
        r"""Compute the conditions on solutions modulo some primes.

        Given a factor $g$ of the polynomial $f$ over some galois
        field extension $K$ such that we have .. MATH::

           g = c u x^l

        for some $c, x \in K$ and unit $u$ in the ring of integers of
        $K$, one can consider this equation modulo all finite primes
        $P$ of $K$. Doing this for all primes above a prime number $p$
        gives us a limited set of values for solutions of the
        diophantine equation modulo $p$. This method computes these
        values for multiple prime numbers $p$ and gives them as
        conditions on the variables of $f$.

        The units chosen in the equation for $g$ are obtained with the
        method :meth:`unit_coeffs` and the computation mentioned above
        is done for each possible unit separately. If for some prime
        number there is no possible values for a solution for a given
        unit, then this unit is omitted for all primes. This makes it
        run this method for multiple primes even if one is only
        interested in the result for a single prime.

        .. NOTE:

        For each prime $P$ of $K$ for which the residue field does not
        have a primitive $l$-th root of unity, the computation of
        possible values does not yield any restrictions. The
        computation is therefore limited to those prime numbers $p$
        for which there is a prime $P$ of $K$ above them for which the
        residue field does have a primitive $l$-th root of unity.

        INPUT:

        - ``K`` -- A galois field extension of the field over which
          $f$ is defined.

        - ``g`` -- A factor of the polynomial $f$ over the field `K`.

        - ``l`` -- A prime number, the exponent to be considered in
          the diophantine equation.

        - ``primes`` -- A list of prime numbers for which the possible
          values modulo that prime should be determined. It can also
          be set to a non-negative integer in which case this list
          will be initialized as all the prime numbers smaller than
          that number.

        - ``c`` -- An element of `K` or None (default: None). This
          element must be such that $g = c u x^l$ for some $x$ in `K`
          and some unit $u$ of the ring of integers of `K`. If set to
          None will be initialized with the method
          :meth:`constant_coeff`.

        - ``bad_primes_val`` -- A tuple of integers, where each
          integer is the valuation of $g$ at the corresponding prime
          in the list returned by :meth:`bad_primes`. This argument
          only has to be provided if `c` is not given.

        OUTPUT:
        
        A dictionary indexed by those prime numbers $p$ in the given
        list of primes for which the number of elements of a residue
        field of a prime above $p$ in `K` is 1 modulo `l`. For each
        prime number $p$ the corresponding value is a condition on the
        variables of $f$ satisfied only by those values of the
        variables for which $g = c u x^l$ can be true for some $x$ in
        `K`, unit $u$ in the ring of integers of `K$ modulo all primes
        above $p$.

        """
        data = self.prime_data(K, g, l, primes, c=c,
                               bad_primes_val=bad_primes_val)
        result = {}
        for p in data:
            T = pAdicTree(variables=self._f.variables(), prime=p, ring=QQ,
                          full=False)
            Tr = T._root
            for val in {val for u in data[p] for val in data[p][u]}:
                Tr.children.add(pAdicNode(pAdics=Tr.pAdics(),
                                          coefficients=val,
                                          full=True))
            result[p] = TreeCondition(T)
        return result

def polynomial_split_on_basis(f, B):
    r"""Decompose a polynomial over a number field into polynomials over
    the rationals.

    Given a (multivariate) polynomial $f$ over a number field $K$ and
    a $\QQ$-basis $b_1, \ldots, b_n$ of $K$, there are unique
    polynomials $g_1, \ldots, g_n$ over the rationals in the same
    variables as $f$ such that .. MATH::

       f = b_1 g_1 + \ldots + b_n g_n.

    This method finds the polynomial $g_1, \ldots, g_n$.

    INPUT:

    - ``f`` -- A (multivariate) polynomial over some number field $K$.

    - ``B`` -- A basis of $K$ over the rationals.

    OUTPUT:

    A list polynomials $g_1, \ldots g_n$ over the rationals such that
    .. MATH::

        f = b_1 g_1 + \ldots + b_n g_n,

    where $b_1, \ldots, b_n$ are the elements of `B`.

    """
    K = f.parent().base_ring()
    M = matrix([K(B[i]).list() for i in range(len(B))]).transpose()
    if not M.is_invertible():
        raise ValueError("%s is not a basis for %s"%(B, K))
    R = f.parent().change_ring(QQ)
    # For each monomial m
    #   M^(-1) * vector(f.monomial_coefficient(m).list())
    # is the vector that expresses the corresponding coefficient
    # of f in terms of the basis B
    monomials = [[cf * R(m)
                  for cf in (M^(-1)*vector(f.monomial_coefficient(m).list()))]
                 for m in f.monomials()]
    return [sum(ls) for ls in zip(*monomials)]
