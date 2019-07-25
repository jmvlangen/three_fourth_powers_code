r"""Basic methods for dealing with p-adic completions of number fields

This file contains the class pAdicBase which is a wrapper for easy
access to functionality needed by more advanced p-adic computational
code.

EXAMPLES::

    sage: pAdics = pAdicBase(QQ, 7)
    sage: pAdics.order()
    Integer Ring
    sage: pAdics.prime()
    7
    sage: pAdics.quotient_ring(3)
    Ring of integers modulo 343
    sage: pi = pAdics.uniformizer(); pi
    7
    sage: pAdics.power_series(2 + 3*pi + 5*pi^2, precision=3)
    [2, 3, 5]

::

    sage: K = QuadraticField(-3)
    sage: pAdics = pAdicBase(K, K.prime_above(7))
    sage: pAdics.order()
    Eisenstein Integers in Number Field in a with defining polynomial x^2 + 3
    sage: pAdics.prime()
    Fractional ideal (-3/2*a - 1/2)
    sage: pAdics.quotient_ring(3)
    Quotient of Eisenstein Integers in Number Field in a with defining polynomial x^2 + 3 by the ideal (9*a + 10)
    sage: pi = pAdics.uniformizer(); pi
    7
    sage: pAdics.power_series(2 + 3*pi + 5*pi^2, precision=3)
    [3*a + 3, 3/2*a + 3/2, 3*a + 3]

AUTHORS:

- Joey van Langen (2019-02-20): initial version

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

from sage.rings.number_field.order import Order
from sage.rings.number_field.number_field import NumberField_generic
from sage.structure.sage_object import SageObject

class pAdicBase(SageObject):
    r"""A class that stores basic information related to p-adic arithmatic.

    p-adic numbers in this context are represented by elements of a
    number field or the rationals modulo a power of some prime ideal,
    or prime number in the case of the rationals.
        
    EXAMPLES::
        
        sage: pAdics = pAdicBase(ZZ, 5)
        sage: pAdics
        p-adics given by Rational Field and (5)
        sage: pAdics.valuation(100)
        2
        
    Example using a number field::
    
        sage: K = QuadraticField(-7)
        sage: pAdics = pAdicBase(K, K.prime_above(2))
        sage: pAdics
        p-adics given by Number Field in a with defining polynomial x^2 + 7 and (-1/2*a + 1/2)
        sage: pAdics.characteristic()
        2

    """
    
    def __init__(self, ring, prime):
        r"""Initializes this object.
        
        INPUT:
        
        - ``ring`` -- A number field or order therein.

        - ``prime`` -- A prime ideal of the maximal order of the
          number field given by the first argument or a generator
          thereof.
          
        EXAMPLES::
            
            sage: pAdicBase(QQ,3)
            p-adics given by Rational Field and (3)
            
        Example using a number field::
        
            sage: K = CyclotomicField(5)
            sage: pAdicBase(K, K.prime_above(5))
            p-adics given by Cyclotomic Field of order 5 and degree 4 and (zeta5 - 1)

        """
        if isinstance(ring, Order):
            ring = ring.number_field()
        if ring == ZZ:
            ring = QQ
        if isinstance(ring, NumberField_generic):
            self._R = ring.maximal_order()
        elif ring == QQ:
            self._R = ZZ
        else:
            raise ValueError("%s is not a number field."%ring)
        if prime in self._R:
            prime = self._R.ideal(prime)
        if prime not in self._R.ideal_monoid() or not prime.is_prime():
            raise ValueError("%s is not a prime ideal of %s."%(prime, self._R))
        self._P = self._R.ideal_monoid()(prime)
        self._ext = dict() # Residue field as a vector space
        
    def number_field(self):
        r"""Return the number field associated to these p-adics.
        
        OUTPUT:

        The number field associated to these p-adics.
        
        EXAMPLE::
        
            sage: K = QuadraticField(7)
            sage: pAdics = pAdicBase(K, K.prime_above(2))
            sage: K == pAdics.number_field()
            True

        """
        if self._R == ZZ:
            return QQ
        else:
            return self._R.number_field()
    
    def order(self):
        r"""Return the maximal order associated to these p-adics.
        
        OUTPUT:

        The maximal order in the number field returned by
        :meth:`number_field`.
        
        EXAMPLES::
        
            sage: K = QuadraticField(-5)
            sage: pAdicBase(K, K.prime_above(17)).order()
            Maximal Order in Number Field in a with defining polynomial x^2 + 5
            
        ::
        
            sage: K = CyclotomicField(7)
            sage: pAdics = pAdicBase(K, K.prime_above(3))
            sage: pAdics.order() == K.ring_of_integers()
            True

        """
        return self._R
        
    def prime_ideal(self):
        r"""Return the prime ideal associated to these p-adics
        
        OUTPUT:

        The prime ideal associated to these p-adics.
        
        EXAMPLES::
        
            sage: pAdics = pAdicBase(ZZ,13)
            sage: pAdics.prime_ideal()
            Principal ideal (13) of Integer Ring
            
        ::
        
            sage: K = QuadraticField(-1)
            sage: pAdics = pAdicBase(K, K.prime_above(7))
            sage: pAdics.prime_ideal() == K.prime_above(7)
            True

        """
        return self._P

    def prime(self):
        r"""Return the prime associated to these p-adics.

        This is useful for methods that accept a different kind of
        argument when working over the rationals instead of a number
        field.

        OUTPUT:

        The prime ideal associated to these p-adics if the associated
        number field is not $\Q$. Otherwise simply the prime number that
        generates that prime ideal.

        EXAMPLES::

            sage: pAdics = pAdicBase(ZZ, 13)
            sage: pAdics.prime()
            13
            sage: pAdics.prime_ideal()
            Principal ideal (13) of Integer Ring

        ::

            sage: K = QuadraticField(-2)
            sage: pAdics = pAdicBase(K, K.prime_above(5))
            sage: pAdics.prime()
            Fractional ideal (5)
            sage: pAdics.prime_ideal()
            Fractional ideal (5)

        .. SEEALSO::

            :meth:`prime_ideal`

        """
        P = self.prime_ideal()
        if self._R == ZZ:
            return P.gens()[0]
        else:
            return P

    def prime_below(self, R):
        r"""Give the prime that lies below the prime of these p-adics.

        INPUT:
        
        - ``R`` -- A subring of the number field of these p-adics.

        OUTPUT:

        A prime of the field of fractions of R that lies below the
        prime stored in this pAdicBase.

        EXAMPLES::

            sage: K = QuadraticField(7)
            sage: pAdics = pAdicBase(K, K.prime_above(3))
            sage: pAdics.prime_below(ZZ)
            3

        ::

            sage: K = QuadraticField(5)
            sage: L = CyclotomicField(5)
            sage: pAdics = pAdicBase(L, L.prime_above(11))
            sage: P = pAdics.prime_below(K); P
            Fractional ideal (3/2*a - 1/2)

        """
        K = R.fraction_field()
        L = self.number_field()
        Q = self.prime_ideal()
        if L is QQ:
            p = Q.gens()[0]
        else:
            p = Q.smallest_integer()
        if K == QQ:
            return p
        ls = K.embeddings(L)
        if len(ls) < 1:
            raise ValueError("%s is not a subring of %s"%(R, L))
        iota = ls[0]
        for P in K.primes_above(p):
            PL = L.ideal([iota(g) for g in P.gens()])
            if Q in L.primes_above(PL):
                return P
        raise ValueError("No prime in %s lies below %s"%(K, Q))

    def pAdics_below(self, R):
        r"""Give the p-Adics that lies below this one.

        INPUT:

        - ``R`` -- A subring of the number field of this pAdicBase.

        OUTPUT:

        A pAdicBase object over the ring of fractions of R such that
        its prime lies below the prime stored in this pAdicBase.

        EXAMPLE::

            sage: K = QuadraticField(5)
            sage: L = CyclotomicField(5)
            sage: pAdics = pAdicBase(L, L.prime_above(11)); pAdics
            p-adics given by Cyclotomic Field of order 5 and degree 4 and (zeta5^3 + 2*zeta5^2 + zeta5 + 2)
            sage: pAdics.pAdics_below(K)
            p-adics given by Number Field in a with defining polynomial x^2 - 5 and (3/2*a - 1/2)
            sage: pAdics.pAdics_below(QQ)
            p-adics given by Rational Field and (11)

        .. SEEALSO::

            :meth:`prime_below`
        """
        return pAdicBase(R.fraction_field(), self.prime_below(R))

    @cached_method
    def uniformizer(self):
        r"""Return a uniformizer associated to these p-adics.
        
        OUTPUT:

        An element of the prime ideal returned by :func:`prime_ideal`
        that has valuation 1 with respect to this prime ideal.
        
        EXAMPLE:
        
            sage: K.<a> = QuadraticField(10)
            sage: P = K.ideal(3, a + 1)
            sage: pAdics = pAdicBase(K, P)
            sage: pi = pAdics.uniformizer(); pi
            3
            sage: pAdics.valuation(pi)
            1

        .. SEEALSO::

            :meth:`prime_ideal`
            :meth:`valuation`

        """
        if self._R == ZZ:
            return self._P.gens()[0]
        else:
            for g in self._P.gens():
                if g.ord(self._P) == 1:
                    return g
        raise ValueError("The ideal %s has no uniformizer"%(self._P,))
            
    def valuation(self, x):
        r"""Calculate the valuation of some element.
        
        INPUT:
        
        - ``x`` -- An element of the number field returned by
          :func:`number_field`.
        
        OUTPUT:

        The valuation of ``x`` with respect to the prime ideal of
        these p-adics, i.e. the order of the prime ideal returned by
        :func:`prime_ideal` in the prime factorization of ``x``.
        
        EXAMPLES::
        
            sage: pAdics = pAdicBase(QQ, 2)
            sage: pAdics.valuation(24)
            3
            sage: pAdics.valuation(3/2)
            -1
            
        ::
            
            sage: K.<a> = QuadraticField(-3)
            sage: pAdics = pAdicBase(K, K.prime_above(7))
            sage: pAdics.valuation(18*a + 20)
            3
            sage: pAdics.valuation((9*a - 3)/14)
            -1

        """
        x = self.number_field()(x)
        if self._R == ZZ:
            return x.ord(self.uniformizer())
        else:
            return x.ord(self.prime_ideal())
            
    def _power_series(self, x, prec, F, pi):
        if prec > 0:
            c0 = F.lift(F(x))
            return [c0] + self._power_series((x-c0)/pi, prec-1, F, pi)
        else:
            return []
            
    def power_series(self, x, precision=10):
        """r Write an element x as a power series in the uniformizer.
        
        INPUT:
        
        - ``x`` -- An element of the number field associated to these
          p-adics, which has non-negative valuation with respect to
          the prime ideal returned by :func:`prime_ideal`.

        - ``precision`` -- A strictly positive integer (default: 10)
          which indicates to what order the power series should
          extend. Note that precision 10 will result in a power series
          with highest power of the uniformizer equal to 9.
          
        OUTPUT:

        A list of elements $c_i$, such that .. MATH::
        
            \sum_{i=0}^{k-1} c_i * \pi^i \equiv x \text{(mod} P^k),
            
        where $P$ is the prime ideal associated to these p-adics and $\pi$
        is its uniformizer as returned by :meth:`uniformizer`. Furthermore
        all `c_i` are chosen from the set returned by :meth:`representatives`

        EXAMPLE::

            sage: K = CyclotomicField(3)
            sage: pAdics = pAdicBase(K, K.prime_above(7))
            sage: c = pAdics.power_series(8); c
            [1, 5, 6, 2, 3, 3, 3, 3, 3, 3]
            sage: pi = pAdics.uniformizer(); pi
            zeta3 + 3
            sage: a = sum(c[i]*pi^i for i in range(10)); a
            10907*zeta3 - 22074
            sage: pAdics.valuation(a - 8)
            10

        .. SEEALSO::

            :meth:`prime_ideal`
            :meth:`uniformizer`
            :meth:`representatives`

        """
        if self.valuation(x) < 0:
            raise ValueError(str(x) + " is not integral with respect to " +
                             str(self.prime_ideal()))
        if precision not in ZZ or precision <= 0:
            raise ValueError(str(precision) +
                             "is not a strictly positive integer.")
        return self._power_series(x, precision, self.residue_field(),
                                  self.uniformizer())

    @cached_method
    def residue_field(self):
        r"""Return the residue field associated to these p-adics.
        
        OUTPUT:

        The residue field of the prime ideal associated with these
        p-adics.
        
        EXAMPLES::
        
            sage: pAdicBase(ZZ, 5).residue_field()
            Residue field of Integers modulo 5
            
        ::
        
            sage: K = QuadraticField(-1)
            sage: pAdicBase(K, K.prime_above(5)).residue_field()
            Residue field of Fractional ideal (-a - 2)

        .. SEEALSO::

            :meth:`prime_ideal`

        """
        return self.number_field().residue_field(self._P)
    
    def representatives(self, width=1):
        r"""Give a generator of reprentatives of a vector space over the
        residue field.
        
        INPUT:
        
        - ``width`` -- A strictly positive integer (default: `1`) that
          determines the rank of the module.
          
        OUTPUT:

        A generator of tuples of length `width` containing integral
        elements of the number field associated with these p-adics,
        such that the reduction of these tuples modulo the prime ideal
        associated with these p-adics correspond one to one with the
        elements of a module over the residue field of that prime
        ideal of rank `width`.
        
        EXAMPLES:
        
        Determining the squares modulo 11. Note that the function
        returns tuples, hence we have to take the first argument::
        
            sage: pAdics = pAdicBase(ZZ, 11)
            sage: F = pAdics.residue_field()
            sage: squares = []
            sage: for x in pAdics.representatives():
            ....:     x2 = F(x[0]^2)
            ....:     if x2 not in squares:
            ....:         squares.append(x2)
            ....: squares.sort();
            ....: print squares
            ....:
            [1, 3, 4, 5, 9]
            
        Calculating representatives of possible roots modulo a prime
        ideal for a polynomial in two variables::
        
            sage: K = QuadraticField(5)
            sage: pAdics = pAdicBase(K, K.prime_above(11))
            sage: R = pAdics.order()
            sage: S.<x,y> = R[]
            sage: f = x^3 - y^2
            sage: roots = []
            sage: for z in pAdics.representatives(width=2):
            ....:     if pAdics.valuation(f(z)) > 0:
            ....:         roots.append(z)
            ....: print roots
            ....:
            [(0, 0), (7/2*a + 7/2, 7/2*a + 7/2), (a + 1, 3/2*a + 3/2), (3*a + 3, 5*a + 5), (5*a + 5, 3*a + 3), (4*a + 4, a + 1), (4*a + 4, 9/2*a + 9/2), (5*a + 5, 5/2*a + 5/2), (3*a + 3, 1/2*a + 1/2), (a + 1, 4*a + 4), (7/2*a + 7/2, 2*a + 2)]

        ..SEEALSO ::

            :meth:`prime_ideal`
            :meth:`residue_field`
            :meth:`number_field`
            :meth:`order`

        """
        if width not in ZZ or width <= 0:
            raise ValueError("width should be a strictly positive integer, not %s."%(width,))
        for cfs in self.residue_field()**width:
            yield tuple([self.residue_field().lift(c) for c in cfs])
            
    def size_residue_field(self):
        r"""Return the size of the residue field associated to these p-adics.
        
        OUTPUT:

        The cardinality of the residue field of the prime ideal associated
        to these p-adics.
        
        EXAMPLE::
        
            sage: K = QuadraticField(3)
            sage: pAdics = pAdicBase(K, K.prime_above(5))
            sage: pAdics.size_residue_field()
            25

        .. SEEALSO::

            :meth:`prime_ideal`
            :meth:`residue_field`

        """
        return self.residue_field().cardinality()
        
    def characteristic(self):
        r"""Give the characteristic associated to these p-adics.
        
        OUTPUT:

        The characteristic of the residue field of the prime ideal
        associated to these p-adics, i.e. the smallest prime number in
        ZZ that is in that prime ideal.
        
        EXAMPLE::
            
            sage: K = CyclotomicField(11)
            sage: pAdics = pAdicBase(K, K.prime_above(7))
            sage: pAdics.characteristic()
            7
        
        .. SEEALSO::

            :meth:`prime_ideal`
            :meth:`residue_field`

        """
        return self.residue_field().characteristic()
        
    def quotient_ring(self, n, names='param'):
        r"""Return the quotient ring by a power of the prime ideal associated
        to these p-adics.
        
        INPUT:
        
        - ``n`` -- A non-negative integer determining which power of
          the prime ideal should be quotiented out.

        - ``names`` -- An identifier or list of identifiers (default:
          'param') that can be used as the names of quotient
          variables.
          
        OUTPUT:

        The quotient of the ring of integers of the number field
        associated with these p-adics by $P^n$ where $P$ is the prime
        ideal associated to these p-adics.
        
        EXAMPLES::
        
            sage: pAdicBase(ZZ, 3).quotient_ring(2)
            Ring of integers modulo 9
            
        Another example over a number field::
        
            sage: K = QuadraticField(-2)
            sage: pAdics = pAdicBase(K, K.prime_above(7))
            sage: pAdics.quotient_ring(3, names='a')
            Quotient of Maximal Order in Number Field in a with defining polynomial x^2 + 2 by the ideal (343)

        .. SEEALSO::

            :meth:`prime_ideal`
            :meth:`order`
            :meth:`number_field`

        """
        if n not in ZZ or n < 0:
            raise ValueError("n should be a non-negative integer, not %s."%(n,))
        if self._R == ZZ:
            return ZZ.quotient((self._P**n).gens()[0])
        else:
            return self._R.quotient(self._P**n, names=names)
    
    def zero(self):
        r"""Give the zero element associated to these p-adics.
        
        OUTPUT:

        The zero element of the ring of integers of the number field
        associated with these p-adics.
        
        EXAMPLE::
        
            sage: pAdicBase(ZZ, 11).zero()
            0

        .. SEEALSO::

            :meth:`number_field`
            :meth:`order`

        """
        return self._R.zero()
        
    def _repr_(self):
        return ("p-adics given by " + str(self.number_field()) +
                " and " + str(self._P._repr_short()))
                                                           
    def is_extension_of(self, other):
        r"""Determine whether these p-adics extend another.
        
        We say that one pAdicBase object extends another if the field
        of the first is an extension of the field of the other and the
        prime of the second lies below the prime of the first.
          
        INPUT:
        
        - ``other`` -- A pAdicBase object.
        
        OUTPUT:

        True if this pAdicBase object extends the pAdicBase object
        given, False in all other cases.
        
        EXAMPLES::
        
            sage: K = QuadraticField(-7)
            sage: p1 = pAdicBase(QQ, 7)
            sage: P = K.prime_above(7)
            sage: p2 = pAdicBase(K, P)
            sage: p2.is_extension_of(p1)
            True
            
        If one field does not extend another::
        
            sage: K = QuadraticField(-3)
            sage: L = QuadraticField(5)
            sage: P = K.prime_above(2)
            sage: Q = L.prime_above(2)
            sage: p1 = pAdicBase(K, P)
            sage: p2 = pAdicBase(L, Q)
            sage: p1.is_extension_of(p2)
            False
        
        If the primes do not match::
        
            sage: K = CyclotomicField(3)
            sage: P = K.prime_above(3)
            sage: p1 = pAdicBase(QQ, 2)
            sage: p2 = pAdicBase(K, P)
            sage: p2.is_extension_of(p1)
            False

        .. SEEALSO::

            :meth:`number_field`
            :meth:`prime_ideal`

        """
        if not isinstance(other, pAdicBase):
            return false
        L = self.number_field()
        iota_ls = other.number_field().embeddings(L)
        if len(iota_ls) < 1:
            return false
        P = other.prime_ideal()
        if other.number_field() == QQ:
            if self.number_field() == QQ:
                return P == self.prime_ideal()
        PL = L.ideal([iota_ls[0](a) for a in P.gens()])
        return self.prime_ideal() in L.primes_above(PL)
        
    def extension_multiplicity(self, other):
        r"""Give the extension multiplicity of some pAdicBase object over
        another.
        
        If some pAdicBase object extends another, then its extension
        multiplicity is the ramification index of its prime ideal over
        the other's prime ideal.
        
        INPUT:
        
        - ``other`` -- A pAdicBase object that extends this pAdicBase
          object, or of which this pAdicBase object is an extension.
          
        OUTPUT:

        A strictly positive integer equal to the valuation of a
        uniformizer. The valuation will be of the pAdicBase object
        that extends the other and the uniformizer will be from the
        pAdicBase object that is extended. By default will assume
        that this pAdicBase object extends the other.
        
        EXAMPLES::
        
            sage: K = QuadraticField(-5)
            sage: P = K.prime_above(5)
            sage: p1 = pAdicBase(QQ, 5)
            sage: p2 = pAdicBase(K, P)
            sage: p1.extension_multiplicity(p2)
            2
            sage: P.ramification_index()
            2
        
        An example not over QQ::
            
            sage: K = CyclotomicField(4)
            sage: L = CyclotomicField(8)
            sage: P = K.prime_above(3)
            sage: Q = L.prime_above(P)
            sage: p1 = pAdicBase(K, P)
            sage: p2 = pAdicBase(L, Q)
            sage: p1.extension_multiplicity(p2)
            1
        
        It produces the right result when other==self::
        
            sage: K = QuadraticField(3)
            sage: P = K.prime_above(7)
            sage: pAdics = pAdicBase(K, P)
            sage: pAdics.extension_multiplicity(pAdics)
            1

        .. SEEALSO::

            :meth:`is_extension_of`
            :meth:`valuation`
            :meth:`uniformizer`
            :meth:`prime_ideal`
        """
        if self.is_extension_of(other):
            iota = other.number_field().embeddings(self.number_field())[0]
            return self.valuation(iota(other.uniformizer()))
        elif other.is_extension_of(self):
            iota = self.number_field().embeddings(other.number_field())[0]
            return other.valuation(iota(self.uniformizer()))
        else:
            raise ValueError(str(self) + " and " + str(other) +
                             " do not extend one another.")
    
    def _extension_vector_space(self, other):
        r"""An implementation of :meth:`extension_vector_space`"""
        K = other.number_field()
        P = other.prime_ideal()
        key = (K,P)
        if key not in self._ext:
            F = self.residue_field()
            L = self.number_field()
            gamma = F.multiplicative_generator()
            VF = F.vector_space()
            G = other.residue_field()
            p = self.characteristic()
            VG = G.vector_space()
            m = VG.rank()
            n = ZZ(VF.rank()/m)
            WG = G^n
            
            e = [G(a) for a in VG.basis()] # Basis of G
            Fe = [F(L(G.lift(ei))) for ei in e] # Embedding of that basis in F
            # Making the matrix that describes the map VG^n -> VF
            # Note the matrix will be on the right of the vector
            # in multiplication!
            MF = Fe
            gammaFe = Fe
            for i in range(1,n):
                gammaFe = [gamma * ei for ei in gammaFe]
                MF.extend(gammaFe)
            M = matrix([VF(MFi._vector_()) for MFi in MF])
            N = M.inverse() # The matrix describing VF -> VG^n
            
            def phi(x):
                x = F(x)
                Vx = VF(x._vector_()) * N
                result = [G(VG(Vx[m*i:m*(i+1)])) for i in range(n)]
                return WG(result)
            
            self._ext[key] = phi
        return self._ext[key]
                                                                     
    def extension_vector_space(self, other):
        r"""Give the residue field of this pAdicBase object as a vector space
        over another.
        
        If some p-adics extends another p-adics, then the residue
        field of the first is a field extension of the residue field
        of the second, hence naturally a vector space over the latter.
        
        INPUT:
        
        - ``other`` - A pAdicBase object which is an extension of this
          pAdicBase object or which this pAdicBase object extends.
          
        OUTPUT:

        A $G$-vectorspace isomorphism $F \to G^n$, where $F$ and $G$
        are the residue fields of the p-adics that extends the other
        and the p-adics that is extended respectively. Note that by
        default we will assume that the p-adics of this object extends
        the other.

        EXAMPLE::

            sage: L = CyclotomicField(12)
            sage: pAdicsL = pAdicBase(L, L.prime_above(3))
            sage: pAdicsQ = pAdicsL.pAdics_below(QQ)
            sage: F = pAdicsL.residue_field()
            sage: phi = pAdicsL.extension_vector_space(pAdicsQ)
            sage: [phi(a) for a in F]
            [(0, 0), (1, 2), (2, 2), (0, 1), (2, 0), (2, 1), (1, 1), (0, 2), (1, 0)]

        """
        if self.is_extension_of(other):
            return self._extension_vector_space(other)
        elif other.is_extension_of(self):
            return other._extension_vector_space(self)
        else:
            raise ValueError(str(self) + " and " + str(other) +
                             " do not extend one another.")
        
    def __eq__(self, other):
        return isinstance(other, pAdicBase) \
               and other.order() == self.order() \
               and other.prime_ideal() == self.prime_ideal()
           
    def __ne__(self, other):
        return not isinstance(other, pAdicBase) \
               or other.order() != self.order() \
               or other.prime_ideal() != self.prime_ideal()
