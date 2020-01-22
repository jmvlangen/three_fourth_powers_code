r"""Classes to work with Frey-Hellegouarch curves.

A Frey-Hellegouarch curve, often referred to simply as a Frey curve,
is an elliptic curve of which the coefficients depend on an (unknown)
solution of a diophantine equation. For our purposes a Frey curve will
be an elliptic curve defined over a ring $R$, that is a (multivariate)
polynomial ring over some number field $L$. The variables of $R$ are
assumed to take on undetermined values in the ring of integers of some
subfield $K$ of $L$, which might satisfy some constraints. These
variables are known as the parameters of the Frey curve.

This file provides two variants of Frey curves. The class
:class:`FreyCurve` provides the basic implementation of a Frey
curve. However computing newforms for such a Frey curve only works if
its defined over the rationals. The class :class:`FreyQcurve` extends
the class :class:`FreyCurve` and the class :class:`Qcurve` and
provides a way to work with Frey curves that are also $\Q$-curves.

EXAMPLES:

TODO

AUTHORS:

- Joey van Langen (2019-03-06): initial version

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
from sage.schemes.elliptic_curves.ell_generic import EllipticCurve_generic
from sage.rings.polynomial.polynomial_ring import is_PolynomialRing
from sage.rings.polynomial.multi_polynomial_ring_base import is_MPolynomialRing
from sage.rings.morphism import RingHomomorphism_from_base

from sage.schemes.elliptic_curves.ell_local_data import EllipticCurveLocalData
from sage.schemes.elliptic_curves.kodaira_symbol import KodairaSymbol
from sage.schemes.elliptic_curves.kodaira_symbol import KodairaSymbol_class

from sage.rings.number_field.number_field import is_NumberField

class FreyCurve(EllipticCurve_generic):
    r"""A Frey-Hellegouarch curve.

    A Frey-Hellegouarch curve, or simply a Frey curve, is an elliptic
    curve defined over a (multivariate) polynomial ring $R$ defined
    over some number field $L$. The variables of $R$ are assumed to
    have undetermined values in the ring of integers of some subfield
    $K$ of $L$ and are considered to be parameters of $E$. Therefore
    this elliptic curve is considered as an elliptic curve over $L$.

    This class provides some functionality to compute with this
    elliptic curve as if it is defined over the number field
    $L$. Since the answer of some of these computations might depend
    on the values of the parameters, the result is often given as
    :class:`ConditionalValue`. Most methods also given te option of
    providing additional constraints on the parameters in the form of
    instances of :class:`Condition` and this curve can also internally
    stores a condition on the parameters which is used as a default
    restraint.

    EXAMPLES:

    TODO

    """
    def __init__(self, curve, parameter_ring=ZZ, condition=None):
        r"""Initialize a Frey curve

        INPUT:

        - ``curve`` -- An elliptic curve or any argument that would
          produce such a curve when passed to the constructor
          :func:`EllipticCurve`. The elliptic curve should be defined
          over some (multivariate) polynomial ring $R$ which in turn
          is defined over some number field $L$. This will be the Frey
          curve.

        - ``parameter_ring`` -- The ring of integers of a subfield $K$
          of $L$ (default: ZZ). This is the ring in which the
          variables of the polynomial ring over which this curve is
          defined can take values.

        - ``condition`` -- An instance of :class:`Condition` or None
          (default: None) giving a condition which must hold for the
          values of the variables of $R$. If set to None will assume
          that all values for these variables are allowed.

        """
        if not isinstance(curve, EllipticCurve_generic):
            curve = EllipticCurve(curve)
        S = curve.base_ring()
        if not (is_PolynomialRing(S) or is_MPolynomialRing(S)):
            raise ValueError("The coefficient ring " + str(S) +
                             " is not a polynomial ring.")
        base = S.base_ring()
        EllipticCurve_generic.__init__(self, S, curve.a_invariants())
        self._R = parameter_ring
        if self._R == ZZ:
            self._R_to_base = QQ.embeddings(base)[0]
        else:
            self._R_to_base = self._R.number_field().embeddings(base)[0]
        self._condition = condition

    def definition_field(self):
        r"""Give the field over which this Frey curve is defined.

        Even though the Frey curve is defined over some (multivariate)
        polynomial ring $R$ over some number field $L$, since the
        variables of $R$ are assumed to have values in some subfield
        $K$ of $L$ the curve can be assumed to be defined over $L$.

        OUTPUT:
        
        The base ring of the polynomial ring over which this Frey
        curve is defined.

        .. SEE_ALSO::

            :meth:`base_ring`,
            :meth:`parameters`

        """
        return self.base_ring().base()
    
    def parameters(self):
        r"""Give the parameters on which this Frey curve depends.

        OUTPUT:

        The variables of the polynomial ring over which this Frey
        curve is defined.

        .. SEE_ALSO::

            :meth:`base_ring`,
            :meth:`definition_field`

        """
        return self.base().gens()

    def parameter_ring(self):
        r"""Give the ring in which the parameters can take values.

        OUTPUT:

        A ring in which the parameters of this Frey curve take
        values.

        """
        return self._R

    @cached_method
    def primes_of_possible_additive_reduction(self):
        r"""Compute the primes at which this curve could have additive
        reduction.

        Tries to find all the primes that divide both the discriminant
        $D$ and the invariant $c_4$ of this Frey curve. Since both of
        these invariants are elements of a (multivariate) polynomial
        ring $R$ these primes are not necessarily uniquely determined.
        In case an additional condition is needed on the values of the
        variables of the polynomials, a warning will be printed with
        the additional condition required.

        OUTPUT:

        A list of primes of the definition field of this Frey
        curve. In case the definition field is $\QQ$ these will be
        prime numbers. In case it is a number field they will be
        maximal ideals of its ring of integers. In any case they
        satisfy one of the following conditions.

        - If the curve has no parameters, the list will contain all the primes
          dividing the greatest common divisor of $D$ and $c_4$

        - If the curve has one parameter, the list will contain all the
          primes dividing the resultant of $D$ and $c_4$

        - If the curve has two parameters, the parameters will be
          assumed to be coprime and the list will contain all the
          primes dividing the Macaulay resultant of $D$ and $c_4$.
        
        - If the curve has more than two parameters, the list will
          contain all the primes dividing all the coefficients of $D$
          and $c_4$. Furthermore $D$ and $c_4$ will be assumed to be
          coprime.

        """
        R = self.base()
        n = len(R.gens())
        K = R.base()
        c4 = self.c4()
        D = self.discriminant()
        if K.is_subring(QQ):
            if n == 1:
                return QQ(c4.resultant(D)).numerator().prime_factors()
            elif n == 2 and c4.is_homogeneous() and D.is_homogeneous():
                print ("Warning: Assuming that " + str(self.parameters()[0]) +
                       " and " + str(self.parameters()[1]) + " are coprime.")
                return QQ(c4.macaulay_resultant(D)).numerator().prime_factors()
            else:
                N = lcm(lcm(QQ(c).denominator() for c in c4.coefficients()),
                        lcm(QQ(c).denominator() for c in D.coefficients()))
                M = gcd(gcd([ZZ(c) for c in (N * c4).coefficients()]),
                        gcd([ZZ(c) for c in (N * D).coefficients()]))
                result = QQ(M/N).numerator().prime_factors()
                print ("Warning: Assuming that %s and %s "%(c4,D) +
                       " are coprime outside %s."%(tuple(result),))
                return result
        if n == 1:
            return K.ideal(c4.resultant(D)).prime_factors()
        elif n == 2 and c4.is_homogeneous() and D.is_homogeneous():
            print ("Warning: Assuming that " + str(self.parameters()[0]) +
                   " and " + str(self.parameters()[1]) + " are coprime.")
            return K.ideal(c4.macaulay_resultant(D)).prime_factors()
        else:
            I = sum(K.ideal(c) for c in c4.coefficients())
            J = sum(K.ideal(c) for c in D.coefficients())
            result = (I + J).prime_factors()
            print ("Warning: Assuming that %s and %s"%(c4,D) +
                   " are coprime outside %s."%(tuple(P._repr_short()
                                                    for P in result),))
            return result

    @cached_method(key=(lambda self, p, c, v, pc:
                        (p, (self._condition if c is None else c), pc)))
    def _initial_tree(self, prime, condition=None, verbose=False, precision_cap=20):
        r"""Give a p-adic tree of possible values for the parameters.

        INPUT:

        - ``prime`` -- A (maximal) prime ideal of the ring in which
          the parameters take values or any generator thereof if it is
          principal.

        - ``condition`` -- A Condition or None (default: None) giving
          the condition that the parameters of this Frey curve should
          satisfy. If set to None will use the condition stored in
          this FreyCurve instead.

        - ``verbose`` -- A boolean value or an integer (default:
          False). When set to True or any value larger then zero will
          print comments to stdout about the computations being done
          whilst busy. If set to False or 0 will not print such comments.
          If set to any negative value will also prevent the printing of
          any warnings.  A higher value will cause more messages to be
          printed.
        
        OUTPUT:

        A p-adic tree containing all the possible p-adic values of the
        the parameters satisfying the given condition.

        """
        Tfull = pAdicTree(variables=self.parameters(),
                          pAdics=pAdicBase(self._R, prime))
        if condition is None:
            condition = self._condition
        if condition is None:
            return Tfull
        else:
            return condition.pAdic_tree(pAdic_tree=Tfull, verbose=verbose,
                                        precision_cap=precision_cap)

    @cached_method(key=(lambda self, p, c, v, pc:
                        (p, (self._condition if c is None else c), pc)))
    def local_data(self, prime, condition=None, verbose=False,
                   precision_cap=20):
        r"""Give the local data of this curve at a given prime.

        INPUT:

        - ``prime`` -- A prime of the definition field of this Frey
          curve. This should be a prime number if the definition field
          is $\QQ$ or a maximal ideal of the ring of integers
          otherwise.

        - ``condition`` -- A Condition or None (default: None) giving
          the condition that the parameters of this Frey curve should
          satisfy. If set to None will use the condition stored in
          this FreyCurve instead.

        - ``verbose`` -- A boolean value or an integer (default:
          False). When set to True or any value larger then zero will
          print comments to stdout about the computations being done
          whilst busy. If set to False or 0 will not print such comments.
          If set to any negative value will also prevent the printing of
          any warnings.  A higher value will cause more messages to be
          printed.

        - ``precision_cap`` -- A strictly positive integer (default:
          20) giving the maximal precision level to be used in p-Adic
          arithmetic for the parameters.

        OUTPUT:
        
        The local data of this Frey curve at the given prime under the
        given condition on the parameters. This could be a conditional
        value as the local data might depend on the value of the
        parameters in this Frey curve.

        .. SEEALSO::

            :meth:`local_data`,
            :meth:`kodaira_symbol`,
            :meth:`minimal_model`,
            :meth:`conductor_exponent`,
            :meth:`reduction_type`,

        """
        pAdics = pAdicBase(self.definition_field(), prime)
        Tp = self._initial_tree(pAdics.prime_below(self._R),
                                condition=condition,
                                verbose=(verbose-1 if verbose>0 else verbose))
        result = tates_algorithm(self, initial_values=Tp,
                                 coefficient_ring=self.base(), pAdics=pAdics,
                                 verbose=verbose, precision_cap=precision_cap)
        if len(result) == 1:
            return result[0][0]
        else:
            return result

    @cached_method(key=(lambda self, p, c, v, pc:
                        (p, (self._condition if c is None else c), pc)))
    def minimal_model(self, prime, condition=None, verbose=False,
                      precision_cap=20):
        r"""Give a minimal model of this curve at a given prime.

        INPUT:

        - ``prime`` -- A prime of the definition field of this Frey
          curve. This should be a prime number if the definition field
          is $\QQ$ or a maximal ideal of the ring of integers
          otherwise.

        - ``condition`` -- A Condition or None (default: None) giving
          the condition that the parameters of this Frey curve should
          satisfy. If set to None will use the condition stored in
          this FreyCurve instead.

        - ``verbose`` -- A boolean value or an integer (default:
          False). When set to True or any value larger then zero will
          print comments to stdout about the computations being done
          whilst busy. If set to False or 0 will not print such comments.
          If set to any negative value will also prevent the printing of
          any warnings.  A higher value will cause more messages to be
          printed.

        - ``precision_cap`` -- A strictly positive integer (default:
          20) giving the maximal precision level to be used in p-Adic
          arithmetic for the parameters.

        OUTPUT:
        
        An elliptic curve that is a minimal model of this curve at the
        given prime under the given condition on the parameters. This
        could be a conditional value as the minimal model might depend
        on the value of the parameters in this Frey curve.

        .. SEEALSO::

            :meth:`local_data`,

        """
        if self.local_data.is_in_cache(prime, condition, verbose,
                                       precision_cap):
            local_data = self.local_data(prime, condition, verbose,
                                         precision_cap)
            return apply_to_conditional_value(lambda x: x.minimal_model(),
                                              local_data)
        pAdics = pAdicBase(self.definition_field(), prime)
        Tp = self._initial_tree(pAdics.prime_below(self._R), condition,
                                verbose=(verbose-1 if verbose>0 else verbose))
        result = tates_algorithm(self, initial_values=Tp,
                                 coefficient_ring=self.base(), pAdics=pAdics,
                                 verbose=verbose, precision_cap=precision_cap,
                                 only_calculate=['minimal_model'])
        if len(result) == 1:
            return result[0][0][0]
        else:
            return ConditionalValue([(val[0], con) for val, con in result])

    @cached_method(key=(lambda self, p, c, v, pc:
                        (p, (self._condition if c is None else c), pc)))
    def kodaira_symbol(self, prime, condition=None, verbose=False,
                       precision_cap=20):
        r"""Give the kodaira symbol of this curve at a given prime.

        INPUT:

        - ``prime`` -- A prime of the definition field of this Frey
          curve. This should be a prime number if the definition field
          is $\QQ$ or a maximal ideal of the ring of integers
          otherwise.

        - ``condition`` -- A Condition or None (default: None) giving
          the condition that the parameters of this Frey curve should
          satisfy. If set to None will use the condition stored in
          this FreyCurve instead.

        - ``verbose`` -- A boolean value or an integer (default:
          False). When set to True or any value larger then zero will
          print comments to stdout about the computations being done
          whilst busy. If set to False or 0 will not print such comments.
          If set to any negative value will also prevent the printing of
          any warnings.  A higher value will cause more messages to be
          printed.

        - ``precision_cap`` -- A strictly positive integer (default:
          20) giving the maximal precision level to be used in p-Adic
          arithmetic for the parameters.

        OUTPUT:
        
        The KodairaSymbol representing the type of reduction of this
        curve at the given prime for the parameters satisfying the
        given condition. This could be a conditional value as it might
        depend on the value of the parameters in this curve.

        .. SEEALSO::

            :meth:`local_data`,

        """
        if self.local_data.is_in_cache(prime, condition, verbose,
                                       precision_cap):
            local_data = self.local_data(prime, condition, verbose,
                                         precision_cap)
            return apply_to_conditional_value(lambda x: x.kodaira_symbol(),
                                              local_data)
        
        pAdics = pAdicBase(self.definition_field(), prime)
        Tp = self._initial_tree(pAdics.prime_below(self._R),
                                condition=condition,
                                verbose=(verbose-1 if verbose>0 else verbose))
        result = tates_algorithm(self, initial_values=Tp,
                                 coefficient_ring=self.base(), pAdics=pAdics,
                                 verbose=verbose, precision_cap=precision_cap,
                                 only_calculate=['minimal_model'])
        if len(result) == 1:
            return result[0][0][0]
        else:
            return ConditionalValue([(val[0], con) for val, con in result])
    
    @cached_method(key=(lambda self, p, c, v, pc:
                        (p, (self._condition if c is None else c), pc)))
    def conductor_exponent(self, prime, condition=None, verbose=False,
                           precision_cap=20):
        r"""Give the conductor exponent of this curve at a given prime.

        INPUT:

        - ``prime`` -- A prime of the definition field of this Frey
          curve. This should be a prime number if the definition field
          is $\QQ$ or a maximal ideal of the ring of integers
          otherwise.

        - ``condition`` -- A Condition or None (default: None) giving
          the condition that the parameters of this Frey curve should
          satisfy. If set to None will use the condition stored in
          this FreyCurve instead.

        - ``verbose`` -- A boolean value or an integer (default:
          False). When set to True or any value larger then zero will
          print comments to stdout about the computations being done
          whilst busy. If set to False or 0 will not print such comments.
          If set to any negative value will also prevent the printing of
          any warnings.  A higher value will cause more messages to be
          printed.

        - ``precision_cap`` -- A strictly positive integer (default:
          20) giving the maximal precision level to be used in p-Adic
          arithmetic for the parameters.

        OUTPUT:

        The exponent of the conductor of this Frey curve at the given
        prime for parameters satisfying the given condition. This
        could be a conditional value as the conductor exponent might
        depend on the value of the parameters in this Frey curve.

        .. SEEALSO::

            :meth:`local_data`,
            :meth:`conductor`

        """
        if self.local_data.is_in_cache(prime, condition, verbose,
                                       precision_cap):
            local_data = self.local_data(prime, condition, verbose,
                                         precision_cap)
            return apply_to_conditional_value(lambda x:
                                              x.conductor_valuation(),
                                              local_data)
        
        pAdics = pAdicBase(self.definition_field(), prime)
        Tp = self._initial_tree(pAdics.prime_below(self._R),
                                condition=condition,
                                verbose=(verbose-1 if verbose>0 else verbose))
        result = tates_algorithm(self, initial_values=Tp,
                                 coefficient_ring=self.base(), pAdics=pAdics,
                                 verbose=verbose, precision_cap=precision_cap,
                                 only_calculate=['conductor'])
        if(len(result) == 1):
            return result[0][0][0]
        else:
            return ConditionalValue([(val[0], con) for val,con in result])

    @cached_method(key=(lambda self, p, c, v, pc:
                        (p, (self._condition if c is None else c), pc)))
    def reduction_type(self, prime, condition=None, verbose=False,
                       precision_cap=20):
        r"""Give the reduction type of this curve at a given prime.

        INPUT:

        - ``prime`` -- A prime of the definition field of this Frey
          curve. This should be a prime number if the definition field
          is $\QQ$ or a maximal ideal of the ring of integers
          otherwise.

        - ``condition`` -- A Condition or None (default: None) giving
          the condition that the parameters of this Frey curve should
          satisfy. If set to None will use the condition stored in
          this FreyCurve instead.

        - ``verbose`` -- A boolean value or an integer (default:
          False). When set to True or any value larger then zero will
          print comments to stdout about the computations being done
          whilst busy. If set to False or 0 will not print such comments.
          If set to any negative value will also prevent the printing of
          any warnings.  A higher value will cause more messages to be
          printed.

        - ``precision_cap`` -- A strictly positive integer (default:
          20) giving the maximal precision level to be used in p-Adic
          arithmetic for the parameters.

        OUTPUT:

        One of the following values

        - None, if the elliptic curve has good reduction at the given
          prime.

        - 1, if the elliptic curve has split multiplicative reduction
          at the given prime.

        - -1, if the elliptic curve has non-split multiplicative
          reduction at the given prime.

        - 0, if the elliptic curve has additive reduction at the given
          prime.

        If there is multiple options for the possible reductions, will
        return a conditional value instead containing the above values
        and the cases in which these occur.

        .. SEEALSO::

            :meth:`local_data`,
            :meth:`has_good_reduction`,
            :meth:`has_bad_reduction`,
            :meth:`has_additive_reduction`,
            :meth:`has_multiplicative_reduction`,
            :meth:`has_split_multiplicative_reduction`,
            :meth:`has_non_split_multiplicative_reduction`

        """
        if self.local_data.is_in_cache(prime, condition, verbose,
                                       precision_cap):
            local_data = self.local_data(prime, condition, verbose,
                                         precision_cap)
            return apply_to_conditional_value(lambda x: x._reduction_type,
                                              local_data)
        pAdics = pAdicBase(self.definition_field(), prime)
        Tp = self._initial_tree(pAdics.prime_below(self._R),
                                condition=condition,
                                verbose=(verbose-1 if verbose>0 else verbose),
                                precision_cap=precision_cap)
        result = tates_algorithm(self, initial_values=Tp,
                                 coefficient_ring=self.base(), pAdics=pAdics,
                                 verbose=verbose, precision_cap=precision_cap,
                                 only_calculate=['reduction_type'])
        if(len(result) == 1):
            return result[0][0][0]
        else:
            return ConditionalValue([(val[0], con) for val,con in result])

    def has_good_reduction(self, prime, condition=None, verbose=False,
                           precision_cap=20):
        r"""Tell whether this curve has good reduction at a given prime.

        INPUT:

        - ``prime`` -- A prime of the definition field of this Frey
          curve. This should be a prime number if the definition field
          is $\QQ$ or a maximal ideal of the ring of integers
          otherwise.

        - ``condition`` -- A Condition or None (default: None) giving
          the condition that the parameters of this Frey curve should
          satisfy. If set to None will use the condition stored in
          this FreyCurve instead.

        - ``verbose`` -- A boolean value or an integer (default:
          False). When set to True or any value larger then zero will
          print comments to stdout about the computations being done
          whilst busy. If set to False or 0 will not print such comments.
          If set to any negative value will also prevent the printing of
          any warnings.  A higher value will cause more messages to be
          printed.

        - ``precision_cap`` -- A strictly positive integer (default:
          20) giving the maximal precision level to be used in p-Adic
          arithmetic for the parameters.

        OUTPUT:

        True, if this Frey curve has good reduction at the given
        prime.

        False, if this Frey curve has bad reduction at the given
        prime.

        If the answer depends on the chosen parameters for this Frey
        curve, will return a conditional value containing the above
        values and the conditions for which they occur.

        .. SEEALSO::

            :meth:`reduction_type`

        """
        red_type = self.reduction_type(prime, verbose=verbose,
                                       condition=condition,
                                       precision_cap=precision_cap)
        return apply_to_conditional_value(lambda x: (x == None), red_type)

    def has_bad_reduction(self, prime, condition=None, verbose=False,
                          precision_cap=20):
        r"""Tell whether this curve has bad reduction at a given prime.

        INPUT:

        - ``prime`` -- A prime of the definition field of this Frey
          curve. This should be a prime number if the definition field
          is $\QQ$ or a maximal ideal of the ring of integers
          otherwise.

        - ``condition`` -- A Condition or None (default: None) giving
          the condition that the parameters of this Frey curve should
          satisfy. If set to None will use the condition stored in
          this FreyCurve instead.

        - ``verbose`` -- A boolean value or an integer (default:
          False). When set to True or any value larger then zero will
          print comments to stdout about the computations being done
          whilst busy. If set to False or 0 will not print such comments.
          If set to any negative value will also prevent the printing of
          any warnings.  A higher value will cause more messages to be
          printed.

        - ``precision_cap`` -- A strictly positive integer (default:
          20) giving the maximal precision level to be used in p-Adic
          arithmetic for the parameters.

        OUTPUT:

        True, if this Frey curve has bad reduction at the given prime.

        False, if this Frey curve has good reduction at the given
        prime.

        If the answer depends on the chosen parameters for this Frey
        curve will return a conditional value containing the above
        values and the conditions for which they occur.

        .. SEEALSO::

            :meth:`reduction_type`

        """
        red_type = self.reduction_type(prime, verbose=verbose,
                                       condition=condition,
                                       precision_cap=precision_cap)
        return apply_to_conditional_value(lambda x: (x != None), red_type)

    def has_additive_reduction(self, prime, condition=None, verbose=False,
                               precision_cap=20):
        r"""Tell whether this curve has additive reduction at a given prime.

        INPUT:

        - ``prime`` -- A prime of the definition field of this Frey
          curve. This should be a prime number if the definition field
          is $\QQ$ or a maximal ideal of the ring of integers
          otherwise.

        - ``condition`` -- A Condition or None (default: None) giving
          the condition that the parameters of this Frey curve should
          satisfy. If set to None will use the condition stored in
          this FreyCurve instead.

        - ``verbose`` -- A boolean value or an integer (default:
          False). When set to True or any value larger then zero will
          print comments to stdout about the computations being done
          whilst busy. If set to False or 0 will not print such comments.
          If set to any negative value will also prevent the printing of
          any warnings.  A higher value will cause more messages to be
          printed.

        - ``precision_cap`` -- A strictly positive integer (default:
          20) giving the maximal precision level to be used in p-Adic
          arithmetic for the parameters.

        OUTPUT:

        True, if this Frey curve has additive reduction at the given
        prime.

        False, if this Frey curve does not have additive reduction at
        the given prime.

        If the answer depends on the chosen parameters for this Frey
        curve will return a conditional value containing the above
        values and the conditions for which they occur.

        .. SEEALSO::

            :meth:`reduction_type`

        """
        red_type = self.reduction_type(prime, verbose=verbose,
                                       condition=condition,
                                       precision_cap=precision_cap)
        return apply_to_conditional_value(lambda x: (x == 0), red_type)

    def has_split_multiplicative_reduction(self, prime, condition=None,
                                           verbose=False, precision_cap=20):
        r"""Tell whether this curve has split multiplicative reduction at a
        given prime.

        INPUT:

        - ``prime`` -- A prime of the definition field of this Frey
          curve. This should be a prime number if the definition field
          is $\QQ$ or a maximal ideal of the ring of integers
          otherwise.

        - ``condition`` -- A Condition or None (default: None) giving
          the condition that the parameters of this Frey curve should
          satisfy. If set to None will use the condition stored in
          this FreyCurve instead.

        - ``verbose`` -- A boolean value or an integer (default:
          False). When set to True or any value larger then zero will
          print comments to stdout about the computations being done
          whilst busy. If set to False or 0 will not print such comments.
          If set to any negative value will also prevent the printing of
          any warnings.  A higher value will cause more messages to be
          printed.

        - ``precision_cap`` -- A strictly positive integer (default:
          20) giving the maximal precision level to be used in p-Adic
          arithmetic for the parameters.

        OUTPUT:

        True, if this Frey curve has split multiplicative reduction at
        the given prime.

        False, if this Frey curve does not have split multiplicative
        reduction at the given prime.

        If the answer depends on the chosen parameters for this Frey
        curve will return a conditional value containing the above
        values and the conditions for which they occur.

        .. SEEALSO::

            :meth:`reduction_type`

        """
        red_type = self.reduction_type(prime, verbose=verbose,
                                       condition=condition,
                                       precision_cap=precision_cap)
        return apply_to_conditional_value(lambda x: (x == 1), red_type)

    def has_non_split_multiplicative_reduction(self, prime, condition=None,
                                               verbose=False,
                                               precision_cap=20):
        r"""Tell whether this curve has non-split multiplicative reduction at
        a given prime.

        INPUT:

        - ``prime`` -- A prime of the definition field of this Frey
          curve. This should be a prime number if the definition field
          is $\QQ$ or a maximal ideal of the ring of integers
          otherwise.

        - ``condition`` -- A Condition or None (default: None) giving
          the condition that the parameters of this Frey curve should
          satisfy. If set to None will use the condition stored in
          this FreyCurve instead.

        - ``verbose`` -- A boolean value or an integer (default:
          False). When set to True or any value larger then zero will
          print comments to stdout about the computations being done
          whilst busy. If set to False or 0 will not print such comments.
          If set to any negative value will also prevent the printing of
          any warnings.  A higher value will cause more messages to be
          printed.

        - ``precision_cap`` -- A strictly positive integer (default:
          20) giving the maximal precision level to be used in p-Adic
          arithmetic for the parameters.

        OUTPUT:

        True, if this Frey curve has non-split multiplicative
        reduction at the given prime.

        False, if this Frey curve does not have non-split
        multiplicative reduction at the given prime.

        If the answer depends on the chosen parameters for this Frey
        curve will return a conditional value containing the above
        values and the conditions for which they occur.

        .. SEEALSO::

            :meth:`reduction_type`

        """
        red_type = self.reduction_type(prime, verbose=verbose,
                                       condition=condition,
                                       precision_cap=precision_cap)
        return apply_to_conditional_value(lambda x: (x == -1), red_type)

    def has_multiplicative_reduction(self, prime, condition=None,
                                     verbose=False, precision_cap=20):
        r"""Tell whether this curve has multiplicative reduction at a given
        prime.

        INPUT:

        - ``prime`` -- A prime of the definition field of this Frey
          curve. This should be a prime number if the definition field
          is $\QQ$ or a maximal ideal of the ring of integers
          otherwise.

        - ``condition`` -- A Condition or None (default: None) giving
          the condition that the parameters of this Frey curve should
          satisfy. If set to None will use the condition stored in
          this FreyCurve instead.

        - ``verbose`` -- A boolean value or an integer (default:
          False). When set to True or any value larger then zero will
          print comments to stdout about the computations being done
          whilst busy. If set to False or 0 will not print such comments.
          If set to any negative value will also prevent the printing of
          any warnings.  A higher value will cause more messages to be
          printed.

        - ``precision_cap`` -- A strictly positive integer (default:
          20) giving the maximal precision level to be used in p-Adic
          arithmetic for the parameters.

        OUTPUT:

        True, if this Frey curve has multiplicative reduction at the
        given prime.

        False, if this Frey curve does not have multiplicative
        reduction at the given prime.

        If the answer depends on the chosen parameters for this Frey
        curve will return a ConditionalValue containing the above
        values and the conditions for which they occur.

        .. SEEALSO::

            :meth:`reduction_type`

        """
        red_type = self.reduction_type(prime, verbose=verbose,
                                       condition=condition,
                                       precision_cap=precision_cap)
        return apply_to_conditional_value(lambda x: (x == 1 or x == -1),
                                          red_type)
        
    def base_extend(self, R):
        if (hasattr(R, 'domain') and R.domain() == self.definition_field()):
            dom = self.base_ring()
            codom = dom.change_ring(R.codomain())
            F = RingHomomorphism_from_base(dom.Hom(codom), R)
            result = EllipticCurve_generic.base_extend(self, F)
        else:
            result = EllipticCurve_generic.base_extend(self, R)
        if ((is_PolynomialRing(result.base_ring()) or
             is_MPolynomialRing(result.base_ring())) and
            (result.base_ring().variable_names() ==
             tuple(str(v) for v in self.parameters()))):
            return FreyCurve(result, parameter_ring=self._R,
                             condition=self._condition)
        return result

    def specialize(self, values):
        r"""Give this curve for a specific value of the parameters.

        INPUT:

        - ``values`` -- A list or tuple containing as the i-th entry
          the value that the i-th parameter in should have. The order
          of the parameters is the same as that returned by
          :meth:`parameters`. All values should be elements of the
          ring in which the parameters take value.

        OUTPUT:

        The elliptic curve wherein each parameter is replaced with the
        corresponding value of the given list values.

        .. SEEALSO::

            :meth:`parameter_ring`

        """
        a_invs = [a(tuple(self._R_to_base(val) for val in values))
                  for a in self.a_invariants()]
        return EllipticCurve(a_invs)

    def conductor(self, additive_primes=None, condition=None, verbose=False,
                  precision_cap=20):
        r"""Compute the conductor of this Frey curve.

        INPUT:

        - ``additive_primes`` -- A list containing primes of the
          definition field of this curve or None (default: None). The
          primes in this list should be given as prime number if the
          definition field is $\QQ$ or as maximal ideals
          otherwise. This list should include all the primes at which
          this curve could have additive reduction. If set to None
          will compute this by using the method
          :meth:`primes_of_possible_additive_reduction`.

        - ``condition`` -- A Condition or None (default: None) giving
          the condition that the parameters of this Frey curve should
          satisfy. If set to None will use the condition stored in
          this FreyCurve instead.

        - ``verbose`` -- A boolean value or an integer (default:
          False). When set to True or any value larger then zero will
          print comments to stdout about the computations being done
          whilst busy. If set to False or 0 will not print such
          comments.  If set to any negative value will also prevent
          the printing of any warnings.  A higher value will cause
          more messages to be printed.

        - ``precision_cap`` -- A strictly positive integer (default:
          20) giving the maximal precision level to be used in p-Adic
          arithmetic for the parameters.

        OUTPUT:

        A conditional expression that gives the conductor of this Frey
        curve for each possible value of the parameters on which it
        depends. The left side of this expression is some expression
        that gives the part of the conductor at all the primes given
        in `additive_primes`, whilst the right side is a string
        describing how to compute the part of the conductor that is
        coprime to those primes. The latter contains the operator
        Rad_P which refers to taking the radical of an expression
        ignoring those primes in `additive_primes`.

        """
        if additive_primes is None:
            additive_primes = self.primes_of_possible_additive_reduction()
        result = 1
        for P in additive_primes:
            factor = P^self.conductor_exponent(P, condition=condition,
                                               verbose=verbose,
                                               precision_cap=precision_cap)
            if result == 1:
                result = factor
            elif isinstance(factor, ConditionalExpression):
                operator = ConditionalExpression.PRODUCT_OPERATOR
                result = ConditionalExpression(operator, result, factor)
            else:
                result = result * factor
        return ConditionalExpression(ConditionalExpression.PRODUCT_OPERATOR,
                                     result,
                                     "Rad_P( " +
                                     str(self.discriminant().factor()) + " )")
    
    def _trace_of_frobenius(self, pAdics, red_type, condition, verbose,
                            precision_cap):
        r"""Implementation of :meth:`trace_of_frobenius`

        INPUT:

        - `pAdics` -- The p-adics to be used for the Frobenius
          element

        - `red_type` -- The reduction type of this curve

        - `condition` -- A condition on the parameters of this curve

        - `verbose` -- Verbosity argument

        - `precision_cap` -- Bound on the precision of the parameters

        """
        T = condition.pAdic_tree(pAdics=pAdics.pAdics_below(self._R),
                                 verbose=(verbose-1 if verbose>0 else verbose),
                                 precision_cap=precision_cap).root()
        Fp = len(pAdics.residue_field())
        if red_type is None:
            result = {}
            computed = {}
            for N in T.children_at_level(1):
                E = self.specialize(N.representative())
                Ered = E.reduction(pAdics.prime())
                for E2 in computed:
                    a = is_twist(Ered, E2)
                    if a != 0:
                        ap = a * computed[E2]
                        break
                else:
                    Ep = Ered.count_points()
                    ap = 1 + Fp - Ep
                    computed[Ered] = ap
                if ap not in result:
                    result[ap] = pAdicNode(pAdics=N.pAdics(),
                                           width=N.width)
                result[ap].merge(N)
            return result
        elif red_type == 1 or red_type == -1:
            return {red_type*(len(pAdics.residue_field()) + 1): T}
        else:
            raise ValueError("Can not compute trace of frobenius " +
                             "if the curve has additive reduction.")

    def trace_of_frobenius(self, prime, power=1, condition=None,
                           verbose=False, precision_cap=20):
        r"""Compute the trace of a Frobenius element acting on this curve.

        If the elliptic curve has good reduction at the given prime,
        for every prime number $l$ not divisible by that prime the
        $l$-adic galois representation of this curve is unramified at
        that prime and the trace of the Frobenius element at that
        prime is given by this function.

        If the elliptic curve has multiplicative reduction at the
        given prime, for every prime number $l$ not divisible by the
        prime, the mod $l$ galois representation of this curve is
        unramified at that prime if and only if the valuation of the
        discriminant is divisible by $l$. This function returns the
        trace of the Frobenius element at that prime in such a case,
        but does not check whether the valuation of the discriminant
        is divisible by $l$.

        If the elliptic curve has additive reduction, will raise a
        ValueError since the trace of Frobenius is not well-defined in
        that case.

        INPUT:

        - ``prime`` -- A prime of the definition field of this Frey
          curve. This must be a prime number if the definition field
          is $\QQ$ or a maximal ideal of the corresponding ring of
          integers otherwise.

        - ``power`` -- A strictly positive integer (default: 1). If
          set to a value higher than 1 will compute the trace of the
          Frobenius element to the given power instead of the
          Frobenius element itself.

        - ``condition`` -- A Condition or None (default: None) giving
          the condition that the parameters of this Frey curve should
          satisfy. If set to None will use the condition stored in
          this FreyCurve instead.

        - ``verbose`` -- A boolean value or an integer (default:
          False). When set to True or any value larger then zero will
          print comments to stdout about the computations being done
          whilst busy. If set to False or 0 will not print such comments.
          If set to any negative value will also prevent the printing of
          any warnings.  A higher value will cause more messages to be
          printed.

        - ``precision_cap`` -- A strictly positive integer (default:
          20) giving the maximal precision level to be used in p-Adic
          arithmetic for the parameters.

        OUTPUT:

        The the Frobenius element at the given prime to the given
        power under the $l$-adic or mod $l$ reprentation assuming that
        they are unramified. If this would depend on the parameters
        will return a conditional value of possible values instead.

        """
        pAdics = pAdicBase(self.definition_field(), prime)
        if power > 1:
            D = len(pAdics.residue_field())
            T = self.trace_of_frobenius(prime, condition=condition,
                                        verbose=verbose,
                                        precision_cap=precision_cap)
            result = self._power_trace_formula(power)
            return apply_to_conditional_value(lambda t: result(t, D), T)
        if condition is None:
            condition = self._condition
        red_type = self.reduction_type(prime, condition=condition,
                                       verbose=verbose,
                                       precision_cap=precision_cap)
        result = dict()
        if isinstance(red_type, ConditionalValue):
            for val, con in red_type:
                for a, T in self._trace_of_frobenius(pAdics, val, con, verbose,
                                                     precision_cap).iteritems():
                    if a in result:
                        result[a] = result[a].merge(T)
                    else:
                        result[a] = T
        else:
            for a, T in self._trace_of_frobenius(pAdics, red_type, condition,
                                                 verbose,
                                                 precision_cap).iteritems():
                if a in result:
                    result[a] = result[a].merge(T)
                else:
                    result[a] = T
        
        if len(result) == 1:
            return list(result)[0]
        else:
            Tls = [(a, pAdicTree(variables=self.parameters(), root=T))
                   for a, T in result.iteritems()]
            return ConditionalValue([(a, TreeCondition(T)) for a, T in Tls])

    @cached_method
    def _power_trace_formula(self, n):
        r"""Give the formula to compute the trace of a matrix power.

        Given a 2-by-2 matrix $A$, the trace of $A^n$ for some $n \ge
        1$ can be expressed in terms of the trace and determinant of
        $A$ with a formula. This function gives this formula.

        """
        R.<x,y> = QQ[]
        f = x^n + y^n
        return polynomial_to_symmetric(f)

    @cached_method(key=lambda self, add, c, alg, v, prec, path:
                   ((self._condition if c is None else c),
                    (tuple(self.primes_of_possible_additive_reduction())
                     if add is None else tuple(add)), prec))
    def newform_candidates(self, bad_primes=None, condition=None,
                           algorithm='sage', verbose=False, precision_cap=20,
                           path=None):
        r"""Compute newforms that could be associated to this Frey curve.

        Given a Frey curve defined over the rationals, modularity
        tells us that its $l$-adic galois representations are
        isomorphic those arising from some modular form of level equal
        to the conductor of this curve.

        If for all prime numbers $p$ except for those in a finite set
        $S$ the order of $p$ in the discriminant is divisible by $l$
        and the conductor exponent at $p$ is at most $1$, level
        lowering results tell us that the same is true for the mod $l$
        representation, but that the associated newform in this case
        has level equal to the part of the conductor containing the
        primes in $S$. This function will assume we are in this case
        and return all the newforms of this level.

        INPUT:
        
        - ``bad_primes`` -- A list of prime numbers or None (default:
          None). This should be the list of prime numbers $p$ for
          which the order of $p$ in the discriminant is not divisible
          by $l$ or for which the curve has additive reduction. If set
          to None will be initialized as the result of
          :meth:`primes_of_possible_additive_reduction`, which might
          only contain the prime numbers at which the curve has
          additive reduction.

        - ``condition`` -- A Condition or None (default: None) giving
          the condition that the parameters of this Frey curve should
          satisfy. If set to None will use the condition stored in
          this FreyCurve instead.

        - ``algorithm`` -- The algorithm that should be used to
          compute the newforms. For possible options look at the
          function :func:`get_newforms`.

        - ``verbose`` -- A boolean value or an integer (default:
          False). When set to True or any value larger then zero will
          print comments to stdout about the computations being done
          whilst busy. If set to False or 0 will not print such comments.
          If set to any negative value will also prevent the printing of
          any warnings.  A higher value will cause more messages to be
          printed.

        - ``precision_cap`` -- A strictly positive integer (default:
          20) giving the maximal precision level to be used in p-Adic
          arithmetic for the parameters.

        - ``path`` -- An argument that might be required if the
          argument algorithm is set to a particular value. See the
          function :func:`get_newforms` for more explanation.

        OUTPUT:

        A list of newforms $f$ for which the mod $l$ galois
        representation of $f$ and this Frey curve might be
        isomorphic. If this list depends on the values of the
        parameters, returns a conditional value containing the
        possible lists with the associated conditions on the
        parameters.

        """
        if self.definition_field() != QQ:
            raise ValueError("Can only find newforms associated to " +
                             "Frey curves over the rationals.")
        if bad_primes is None and verbose >= 0:
            print ("Warning: The bad primes chosen by default only take into "+
                   "account primes of additive reduction.")
        N = self.conductor(additive_primes=bad_primes, condition=condition,
                           verbose=verbose, precision_cap=precision_cap).left()
        if isinstance(N, ConditionalExpression):
            N = N.value()
        if condition is None:
            condition = self._condition
        return apply_to_conditional_value(lambda level:
                                          get_newforms(level,
                                                       algorithm=algorithm,
                                                       path=path), N)

    def newforms(self, condition=None, bad_primes=None, algorithm='sage',
                 primes=50, verbose=False, precision_cap_conductor=20,
                 precision_cap_reduction=1, path=None):
        r"""Use :meth:`newform_candidates` and :func:`eliminate_by_trace`
        instead.

        INPUT:

        - ``condition`` -- A Condition giving the restrictions on the
          parameters on this Frey curve that should be considered. By
          default this will be set to the condition associated to this
          FreyCurve.

        - ``bad_primes`` -- An iterable containing prime ideals or
          prime numbers, if the field of definition is QQ, that
          contains all the primes at which this curve can have
          additive reduction. If set to None will compute this by
          using the method primes_of_possible_additive_reduction

        - ``algorithm`` -- One of the following values 'sage' -- to
          use sage to compute newforms (default) 'magma' -- to use
          magma to compute newforms

        - ``primes`` -- A list of prime numbers or a strictly positive
          integer (default: 50). This list gives all the primes at
          which the traces of frobenius of the different galois
          representations should be compared. If set to strictly
          positive integer, will be initialized as the list of all
          prime numbers less than the given number.

        - ``verbose`` -- A boolean value or an integer (default:
          False). When set to True or any value larger then zero will
          print comments to stdout about the computations being done
          whilst busy. If set to False or 0 will not print such
          comments.  If set to any negative value will also prevent
          the printing of any warnings.  If this method calls any
          method that accepts an argument verbose will pass this
          argument to it.  If such a method fulfills a minor task
          within this method and the argument verbose was larger than
          0, will instead pass 1 less than the given argument. This
          makes it so a higher value will print more details about the
          computation than a lower one.

        - ``precision_cap_conductor`` -- A strictly positive integer
          (default: 20) giving the maximal precision level to be used
          in p-Adic arithmetic when computing the conductor.

        - ``precision_cap_reduction`` -- A strictly positive integer
          (default: 1) giving the maximal precision level to be used
          in the p-Adic arithmetic when computing the reduction type
          at a given prime. Since this will do a computation for every
          prime lower than prime_cap, this might get very
          computational intensive if set to a value larger than 1.

        - ``path`` -- A string or None (default: None). A parameter
          only used if the algorithm is set to file, in which case
          this should be a path to the file from which to load
          newforms.

        OUTPUT:

        A list consisting of pairs with as first entry a newform that
        has a mod-l representation that has traces of frobenius that
        could match the traces of frobenius of this curve for all
        given primes, different from l. The second entry is an integer
        divisible by all prime numbers l for which this can be true.
        
        If the level of the newform might depend on a choice of
        parameters will instead give a conditional value wherein each
        value is of the form above and each condition corresponds to a
        single possible level.

        """
        if condition is None:
            condition = self._condition
        if bad_primes is None:
            bad_primes = self.primes_of_possible_additive_reduction()
        newforms = self.newform_candidates(bad_primes=bad_primes,
                                           condition=condition,
                                           algorithm=algorithm,
                                           precision_cap=
                                           precision_cap_conductor,
                                           verbose=verbose, path=path)
        if primes in ZZ and primes > 0:
            primes = prime_range(primes)
        primes = list(primes)
        for P in bad_primes:
            if P in ZZ and P in primes:
                primes.remove(P)
            elif P.smallest_integer() in primes:
                primes.remove(P.smallest_integer())
        return eliminate_by_traces(self, newforms, condition=condition,
                                   primes=primes,
                                   precision_cap=precision_cap_reduction,
                                   verbose=(verbose - 1 if verbose > 0
                                            else verbose))
    def _repr_(self):
        """Give a string representation of a Frey curve.

        .. NOTE:

        This is a direct copy from the code included
        in :class:`EllipticCurve_number_field`

        """
        b = self.ainvs()
        a = [z._coeff_repr() for z in b]
        s = "Frey curve defined by "
        s += "y^2 "
        if a[0] == "-1":
            s += "- x*y "
        elif a[0] == '1':
            s += "+ x*y "
        elif b[0]:
            s += "+ %s*x*y "%a[0]
        if a[2] == "-1":
            s += "- y "
        elif a[2] == '1':
            s += "+ y "
        elif b[2]:
            s += "+ %s*y "%a[2]
        s += "= x^3 "
        if a[1] == "-1":
            s += "- x^2 "
        elif a[1] == '1':
            s += "+ x^2 "
        elif b[1]:
            s += "+ %s*x^2 "%a[1]
        if a[3] == "-1":
            s += "- x "
        elif a[3] == '1':
            s += "+ x "
        elif b[3]:
            s += "+ %s*x "%a[3]
        if a[4] == '-1':
            s += "- 1 "
        elif a[4] == '1':
            s += "+ 1 "
        elif b[4]:
            s += "+ %s "%a[4]
        s = s.replace("+ -","- ")
        s += "over %s "%(self.definition_field(),)
        s += "with parameters %s"%(self.parameters(),)
        return s
        
class FreyCurveLocalData(EllipticCurveLocalData):
    r"""The class for the local reduction data of a Frey curve.

    """
    def __init__(self, E, P, conductor_valuation, discriminant_valuation,
                 kodaira_symbol, tamagawa_number, reduction_type):
        r"""Initialize the reduction data for the Frey curve `E` at the
        prime `P`.

        INPUT:

        - ``E`` -- a Frey curve.

        - ``P`` -- a prime of the definition field of `E`, given as a
          prime number if the definition field is $\QQ$ or as a prime
          ideal otherwise.

        - ``conductor_valuation`` -- The valuation of the conductor of
          `E` at the prime `P`.

        - ``discriminant_valuation`` -- The valuation of the
          discriminant of `E` at the prime `P`.

        - ``kodaira_symbol`` -- The Kodaira symbol associated to the
          reduction of `E` at the prime `P`

        - ``tamagawa_number`` -- The Tamagawa number associated to the
          reduction of `E` at the prime `P`.

        - ``reduction_type`` -- The reduction type of `E` at the prime
          `P`, which can be the values: None, for good reduction, 1
          for split multiplicative reduction, -1 for non-split
          multiplicative reduction, and 0 for additive reduction.

        """
        self._set_elliptic_curve(elliptic_curve)
        self._fp = conductor_valuation
        self._val_disc = discriminant_valuation
        if isinstance(kodaira_symbol, KodairaSymbol_class):
            self._KS = kodaira_symbol
        else:
            self._KS = KodairaSymbol(kodaira_symbol)
        self._cp = tamagawa_number
        self._reduction_type = reduction_type
        
    def _set_elliptic_curve(self, elliptic_curve):
        self._Emin = elliptic_curve
        self._Emin_reduced = elliptic_curve
        
    def same_local_model(self, other):
        r"""Tell if the reduction data of this object and another are the same.

        INPUT:

        - ``other`` -- Some object

        OUTPUT:

        True, if `other` is an instance of
        :class:`EllipticCurveLocalData` and contains the same
        reduction data as this object. False, otherwise

        """
        return (isinstance(other, EllipticCurveLocalData) and
                self.prime() == other.prime() and
                self.kodaira_symbol() == other.kodaira_symbol() and
                self.conductor_valuation() == other.conductor_valuation() and
                self.tamagawa_number() == other.tamagawa_number())
        
    def same_elliptic_data(self, other):
        r"""Tell if the data of this object and another are the
        same.

        INPUT:

        - ``other`` -- Some object

        OUTPUT:

        True, if `other` is an instance of
        :class:`EllipticCurveLocalData` and contains the same data as
        this object. False, otherwise

        """
        return (self.same_local_model(other) and
                self.minimal_model == other.minimal_model())
    
    def __eq__(self, other):
        return (isinstance(other, ParametrizedLocalData) and
                self.same_elliptic_data(other))
        
    def __ne__(self, other):
        return (not isinstance(other, ParametrizedLocalData) or
                not self.same_elliptic_data(other))

class FreyQcurve(FreyCurve, Qcurve):
    r"""A Frey-Hellegouarch curve that is also a Q-curve.

    .. SEE_ALSO::

        :class:`FreyCurve`
        :class:`Qcurve`

    """
    def __init__(self, curve, parameter_ring=ZZ, condition=None, isogenies={}):
        r"""Initializes a Frey Q-curve.

        This initialization calls the initialization of both
        :class:`Qcurve` and :class:`FreyCurve`. Note however that for
        the initialization of the first the parameter
        `guessed_degrees` is always set to the empty list as there is
        no good way to guess isogenies of a Frey curve of a given
        degree.

        INPUT:

        - ``curve`` -- An elliptic curve or any argument that would
          produce such a curve when passed to the constructor
          :func:`EllipticCurve`. The elliptic curve should be defined
          over some (multivariate) polynomial ring $R$ which in turn
          is defined over some number field $L$. The Frey curve will
          be this curve with $L$ replaced with the minimal extension
          that is galois over $\QQ$.

        - ``parameter_ring`` -- The ring of integers of a subfield $K$
          of $L$ (default: ZZ). This is the ring in which the
          variables of the polynomial ring over which this curve is
          defined can take values.

        - ``condition`` -- An instance of :class:`Condition` or None
          (default: None) giving a condition which must hold for the
          values of the variables of $R$. If set to None will assume
          that all values for these variables are allowed.

        - ``isogenies`` -- A dictionary (default: {}) with as keys
           elements of the galois group of the definition field of
           this curve and as values data of the corresponding isogeny
           from the galois conjugate of this Q-curve to itself. This
           data can be either an isogeny as a Sage object or a tuple
           of an algebraic integer (defined as an element of some
           number field) and a strictly positive integer, which are
           respectively the $\lambda$ such that the isogeny is $z
           \mapsto \lambda z$ on the complex numbers and the degree of
           the isogeny.

        """
        FreyCurve.__init__(self, curve, parameter_ring=parameter_ring,
                           condition=condition)
        Qcurve.__init__(self, curve, isogenies=isogenies)

    def _init_curve(self, curve):
        r"""Initialize the underlying elliptic curve.

        This overwrites the method found in :class:`Qcurve`, such that
        the methods of that class can work with this curve as if it
        was defined over its definition field, rather than the
        polynomial ring that is its base ring.

        When this method is called most things have already been
        initialized by the initialization from :class:`FreyCurve`, but
        we initialize again to make sure the definition field will be
        galois over $\QQ$.

        """
        K = self.definition_field()
        if not is_NumberField(K):
            raise ValueError("The ring %s is not a number field."%(K,))
        if not K.is_galois():
            Kgal = K.galois_closure(names=K.variable_name() + 'g')
            iota = K.embeddings(Kgal)[0]
            ainvs = [a.change_ring(iota) for a in curve.a_invariants]
            S = self.base().change_ring(Kgal)
            EllipticCurve_generic.__init__(self, S, ainvs)
            self._R_to_base = iota * self._R_to_base

    def definition_field(self):
        r"""Give the field over which this Frey curve is defined.

        Even though the Frey curve is defined over some (multivariate)
        polynomial ring $R$ over some number field $L$, since the
        variables of $R$ are assumed to have values in some subfield
        $K$ of $L$ the curve can be assumed to be defined over $L$.

        OUTPUT:
        
        The base ring of the polynomial ring over which this Frey
        curve is defined.

        .. SEE_ALSO::

            :meth:`base_ring`,
            :meth:`parameters`

        """
        return self.base_ring().base()

    def base_extend(self, R):
        result = FreyCurve.base_extend(self, R)
        if (isinstance(result, FreyCurve) and
            is_NumberField(result.definition_field())):
            K = self.definition_field()
            L = result.definition_field()
            r = K.gen().minpoly().change_ring(L).roots()
            if len(r) > 0:
                return FreyQcurve(result, isogenies=self._isogeny_data(L),
                                  parameter_ring=result._R,
                                  condition=result._condition)
        return result

    def twist(self, gamma):
        r"""Give the twist of this Frey Q-curve by a given element gamma.

        If this curve was given by .. MATH::

            E : y^2 = x^3 + a_2 x^2 + a_4 x + a_6

        the twisted curve is given by .. MATH::
        
            E : y^2 = x^3 + \gamma a_2 x^2 + \gamma^2 a_4 x
                      + \gamma^3 a_6

        INPUT:

        - ``gamma`` -- An element of a number field.

        OUTPUT:
        
        A Frey Q-curve which is the twist of this Q-curve by
        gamma. The definition field of this new curve will be the
        smallest possible field over which it is completely defined as
        a Q-curve.

        """
        K_E = self.complete_definition_field()
        K_gamma = gamma.parent()
        K, iota, gamma_map = composite_field(K_E, K_gamma, give_maps=True)
        gamma = gamma_map(gamma)
        E_map = iota * self._to_Kl
        E = twist_elliptic_curve(self.change_ring(E_map), gamma)
        ainvs = E.a_invariants()
        l = self.isogeny_scalar
        d = self.degree_map
        G = K.galois_group()
        isogenies = dict()
        for s in G:
            L, K_to_L, alpha = field_with_root(K, s(gamma)/gamma,
                                               give_embedding=True)
            isogenies[s] = (K_to_L(iota(l(s))) * alpha, d(s))
        H = [t for t in G if (all(t(isogenies[s][0]) == isogenies[s][0]
                                  for s in G) and
                              all(t(c) == c for a in ainvs
                                  for c in a.coefficients()))]
        Kmin = fixed_field(H)
        if Kmin != K:
            isogenies_min = {}
            G = Kmin.galois_group()
            for s in Kmin.galois_group():
                l, d = isogenies[galois_field_change(s, K)]
                isogenies_min[s] = (Kmin(l), d)
            ainvs = [a.change_ring(Kmin) for a in ainvs]
            im_gens = K_E.gens()[0].minpoly().change_ring(Kmin).roots()
            return FreyQcurve(ainvs, isogenies=isogenies_min,
                              parameter_ring=self._R,
                              condition=self._condition)
        return FreyQcurve(ainvs, isogenies=isogenies,
                          parameter_ring=self._R,
                          condition=self._condition)
    
    def conductor_restriction_of_scalars(self, additive_primes=None,
                                         condition=None, verbose=False,
                                         precision_cap=20):
        r"""Give the conductor of the restriction of scalars of this Frey
        Q-curve.

        INPUT:

        - ``additive_primes`` -- A list containing primes of the
          definition field of this curve or None (default: None). The
          primes in this list should be given as prime number if the
          definition field is $\QQ$ or as maximal ideals
          otherwise. This list should include all the primes at which
          this curve could have additive reduction. If set to None
          will compute this by using the method
          :meth:`primes_of_possible_additive_reduction`.

        - ``condition`` -- A Condition or None (default: None) giving
          the condition that the parameters of this Frey Q-curve
          should satisfy. If set to None will use the condition stored
          in this Frey Q-curve instead.

        - ``verbose`` -- A boolean value or an integer (default:
          False). When set to True or any value larger then zero will
          print comments to stdout about the computations being done
          whilst busy. If set to False or 0 will not print such
          comments.  If set to any negative value will also prevent
          the printing of any warnings.  A higher value will cause
          more messages to be printed.

        - ``precision_cap`` -- A strictly positive integer (default:
          20) giving the maximal precision level to be used in p-Adic
          arithmetic for the parameters.

        OUTPUT:

        The conductor of the restriction of scalars of this curve over
        the decomposition field. This will be a conditional expression
        containing on the left side a (conditional) expression of the
        part of the conductor coming from primes in `additive_primes`,
        whilst the right hand side is a string describing how to
        compute the part of the conductor coming from primes coprime
        to the primes in `additive_primes`. The latter contains the
        operator Rad_P which refers to taking the radical of an
        expression ignoring those primes in additive_primes.

        """
        K0 = self.definition_field()
        K = self.decomposition_field()
        if K0 != K:
            iota = K0.hom([a.minpoly().change_ring(K).roots()[0][0]
                           for a in K0.gens()], K)
            E = self.change_ring(iota)
        else:
            E = self
        if additive_primes is None:
            additive_primes = copy(E.primes_of_possible_additive_reduction())
            for p in K.discriminant().prime_factors():
                for P in K.primes_above(p):
                    if P.ramification_index() > 1 and P not in additive_primes:
                        additive_primes.append(P)
        # Proposition 1 of Milne, On the arithmetic of Abelian varieties
        N = E.conductor(additive_primes=additive_primes,
                        condition=condition,
                        verbose=verbose,
                        precision_cap=precision_cap)
        additive_part = N.left()
        Dsqr = K.discriminant()^2
        if isinstance(additive_part, ConditionalExpression):
            additive_factors = N.left().factors()
            left_factors = {}
            for f in additive_factors:
                for p,e in f.absolute_norm().factor():
                    if e == 1:
                        e = additive_factors[f]
                    else:
                        e = e * additive_factors[f] 
                    if p in left_factors and left_factors[p] != 0:
                        left_factors[p] = left_factors[p] + e
                    elif e != 0:
                        left_factors[p] = e
            disc_factors = Dsqr.factor()
            for p, e in disc_factors:
                if p in left_factors and left_factors[p] != 0:
                    left_factors[p] = left_factors[p] + e
                elif e != 0:
                    left_factors[p] = e
            if hasattr(disc_factors, 'unit') and disc_factors.unit() != 1:
                left = (Dsqr.factor().unit() *
                        product(p^e for p, e in left_factors.iteritems()))
            else:
                left = product(p^e for p,e in left_factors.iteritems())
        else:
            left = additive_part.absolute_norm() * Dsqr
        return ConditionalExpression(N.operator(),
                                     left,
                                     "Norm(" + N.right() +")")

    def newform_levels(self, bad_primes=None, condition=None, verbose=False,
                       precision_cap=20):
        r"""Compute the levels of newforms that could be associated to this
        Frey Q-curve.

        Each non-CM Q-curve is the quotient of a $\Q$-simple variety
        of GL_2-type, which in turn is isogenous to an abelian
        varietyr associated to a newform. The $\lambda$-adic galois
        representation of this newform is isomorphic to the $l$-adic
        galois representation of the Q-curve when restricted to a
        common subgroup of the absolute galois group of $\QQ$. Here
        $\lambda$ is a prime dividing $l$ in the coefficient field of
        the newform.

        The conductor of an abelian variety associated to a newform is
        $N^n$, where $N$ is the level of the newform and $n$ is the
        dimension of the variety. If the Q-curve decomposes, the
        factors of its restriction of scalars form abelian varieties
        of associated newforms. These newforms are directly related to
        the splitting maps of the Q-curves, in the sense that they are
        twists of one another by the inverse of the twist characters
        and their characters are the inverse of the splitting
        characters. Using results about the change in level when
        twisting a newform and the conductor of the restriction of
        scalars, a guess for the levels of the newforms can be made.

        Let $E$ be an elliptic and $P$ be a prime of its decomposition
        field for which the order of $P$ in the discriminant of $E$ is
        divisible by a prime number $l$ and for which $E$ does not
        have additive reduction. In that case is the mod $l$ galois
        representation of $E$ unramified at $P$. In case $E$ is a
        $\Q$-curve and $P$ is not ramified in the decomposition field,
        this implies that the corresponding mod $\lambda$
        representation of an associated newform is unramified at the
        prime number $p$ below $P$. In this case we would be able to
        find a newform of a lower level that has an isomorphic mod
        $\lambda$ representation. To be precise the lower level is the
        part of the level that is coprime to $p$.

        In the case we have a Frey Q-curve $E$ and only a finite set
        $S$ of bad primes of its decompisition field, i.e. primes $P$
        for which the curve $E$ has additive reduction, that ramify in
        the decomposition field or for which their order in the
        discriminat of $E$ is not divisible by $l$, we know by level
        lowering that the mod $l$ representation of $E$ is isomorphic
        to the mod $\lambda$ galois representation of newforms with a
        level only divisible by prime numbers below primes in the set
        $S$. This function computes the possible levels for a given
        set $S$ of bad primes.

        INPUT:
        
        - ``bad_primes`` -- A list of primes of the decomposition
          field of this curve or None (default: None). These primes
          should be given as prime numbers if the decomposition field
          is $\QQ$ or as prime ideal otherwise. This should be the
          list of all the bad primes, i.e. primes for which this curve
          has additive reduction, primes that ramify in the
          decomposition field and primes of which the order in the
          disriminant of this curve is not divisible by $l$. If set to
          None will be initialized as the result of
          :meth:`primes_of_possible_additive_reduction` together with
          all primes that ramify in the decomposition field, which
          might omit some primes for which the discriminant of this
          curve is not an $l$-th power.

        - ``condition`` -- A Condition or None (default: None) giving
          the condition that the parameters of this Frey curve should
          satisfy. If set to None will use the condition stored in
          this FreyCurve instead.

        - ``verbose`` -- A boolean value or an integer (default:
          False). When set to True or any value larger then zero will
          print comments to stdout about the computations being done
          whilst busy. If set to False or 0 will not print such comments.
          If set to any negative value will also prevent the printing of
          any warnings.  A higher value will cause more messages to be
          printed.

        - ``precision_cap`` -- A strictly positive integer (default:
          20) giving the maximal precision level to be used in p-Adic
          arithmetic for the parameters.

        OUTPUT:

        A list of tuples, each tuple representing one of the options
        for the levels of the newforms associated to this Q-curve. The
        $i$-th entry of such a tuple is the level of a newform
        corresponding to the $i$-th conjugacy class of splitting maps,
        as returned by :meth:`splitting_map`.

        If the outcome depends on the values of the parameters, will
        return a conditional value containing such values with the
        appropiate conditions on the parameters.

        """
        if condition is None:
            condition = self._condition
        N = self.conductor_restriction_of_scalars(additive_primes=bad_primes,
                                                  condition=condition,
                                                  verbose=verbose,
                                                  precision_cap=precision_cap)
        N = N.left()
        if isinstance(N, ConditionalExpression):
            N = N.value()
        return apply_to_conditional_value(lambda Ni:
                                          Qcurve.newform_levels(self, N=Ni), N)

    @cached_method(key=lambda self, add, c, alg, prec, v, path:
                   ((self._condition if c is None else c),
                    (tuple(self.primes_of_possible_additive_reduction())
                     if add is None else tuple(add)),
                    prec))
    def newform_candidates(self, bad_primes=None, condition=None,
                           algorithm='sage', verbose=False, precision_cap=20,
                           path=None):
        r"""Compute newforms that could be associated to this Frey Q-curve.

        Each non-CM Q-curve is the quotient of a $\Q$-simple variety
        of GL_2-type, which in turn is isogenous to an abelian
        varietyr associated to a newform. The $\lambda$-adic galois
        representation of this newform is isomorphic to the $l$-adic
        galois representation of the Q-curve when restricted to a
        common subgroup of the absolute galois group of $\QQ$. Here
        $\lambda$ is a prime dividing $l$ in the coefficient field of
        the newform.

        The conductor of an abelian variety associated to a newform is
        $N^n$, where $N$ is the level of the newform and $n$ is the
        dimension of the variety. If the Q-curve decomposes, the
        factors of its restriction of scalars form abelian varieties
        of associated newforms. These newforms are directly related to
        the splitting maps of the Q-curves, in the sense that they are
        twists of one another by the inverse of the twist characters
        and their characters are the inverse of the splitting
        characters. Using results about the change in level when
        twisting a newform and the conductor of the restriction of
        scalars, a guess for the levels of the newforms can be made.

        Let $E$ be an elliptic and $P$ be a prime of its decomposition
        field for which the order of $P$ in the discriminant of $E$ is
        divisible by a prime number $l$ and for which $E$ does not
        have additive reduction. In that case is the mod $l$ galois
        representation of $E$ unramified at $P$. In case $E$ is a
        $\Q$-curve and $P$ is not ramified in the decomposition field,
        this implies that the corresponding mod $\lambda$
        representation of an associated newform is unramified at the
        prime number $p$ below $P$. In this case we would be able to
        find a newform of a lower level that has an isomorphic mod
        $\lambda$ representation. To be precise the lower level is the
        part of the level that is coprime to $p$.

        In the case we have a Frey Q-curve $E$ and only a finite set
        $S$ of bad primes of its decompisition field, i.e. primes $P$
        for which the curve $E$ has additive reduction, that ramify in
        the decomposition field or for which their order in the
        discriminat of $E$ is not divisible by $l$, we know by level
        lowering that the mod $l$ representation of $E$ is isomorphic
        to the mod $\lambda$ galois representation of newforms with a
        level only divisible by prime numbers below primes in the set
        $S$. This function computes the possible levels and all
        newforms at those levels for this curve given such a set $S$.

        INPUT:
        
        - ``bad_primes`` -- A list of primes of the decomposition
          field of this curve or None (default: None). These primes
          should be given as prime numbers if the decomposition field
          is $\QQ$ or as prime ideal otherwise. This should be the
          list of all the bad primes, i.e. primes for which this curve
          has additive reduction, primes that ramify in the
          decomposition field and primes of which the order in the
          disriminant of this curve is not divisible by $l$. If set to
          None will be initialized as the result of
          :meth:`primes_of_possible_additive_reduction` together with
          all primes that ramify in the decomposition field, which
          might omit some primes for which the discriminant of this
          curve is not an $l$-th power.

        - ``condition`` -- A Condition or None (default: None) giving
          the condition that the parameters of this Frey curve should
          satisfy. If set to None will use the condition stored in
          this FreyCurve instead.

        - ``algorithm`` -- The algorithm that should be used to
          compute the newforms. For possible options look at the
          function :func:`get_newforms`.

        - ``verbose`` -- A boolean value or an integer (default:
          False). When set to True or any value larger then zero will
          print comments to stdout about the computations being done
          whilst busy. If set to False or 0 will not print such comments.
          If set to any negative value will also prevent the printing of
          any warnings.  A higher value will cause more messages to be
          printed.

        - ``precision_cap`` -- A strictly positive integer (default:
          20) giving the maximal precision level to be used in p-Adic
          arithmetic for the parameters.

        - ``path`` -- An argument that might be required if the
          argument algorithm is set to a particular value. See the
          function :func:`get_newforms` for more explanation.

        OUTPUT:

        A list of newforms $f$ for which the mod $l$ galosi
        representations of $f$ and this Frey curve might be
        isomorphic. If this list depends on the values of the
        parameters, returns a conditional value containing the
        possible lists with the associated conditions on the
        parameters.

        """
        if condition is None:
            condition = self._condition
        levels = self.newform_levels(bad_primes=bad_primes,
                                      condition=condition,
                                      verbose=(verbose - 1 if verbose > 0
                                               else verbose),
                                      precision_cap=precision_cap)
        return apply_to_conditional_value(lambda levelsi, con:
                                          self._newform_candidates(levelsi,
                                                                   con &
                                                                   condition,
                                                                   algorithm,
                                                                   path,
                                                                   verbose),
                                          levels, use_condition=True,
                                          default_condition=condition)

    def _newform_candidates(self, levels, condition, algorithm, path, verbose):
        r"""Implementation of :meth:`newform_candidates`

        INPUT:

        - ``levels`` -- List of possible levels for the newforms

        - ``condition`` -- The condition on the parameters to get
          these levels

        - ``algorithm`` -- The argument `algorithm`

        - ``path`` -- The argument ``path``

        - ``verbose`` -- Verbosity argument

        """
        result = []
        done_levels = []
        characters = [(eps^(-1)).primitive_character()
                      for eps in self.splitting_character('conjugacy')]
        for levelsi in levels:
            level, eps, Lbeta = min(zip(levelsi,
                                        characters,
                                        self.splitting_image_field('conjugacy')),
                                    key=lambda x: x[0])
            if (level, eps, Lbeta) in done_levels:
                continue # Already computed, continue on with the next
            if verbose > 0:
                print "Computing newforms of level %s and character %s"%(level, eps)
            result.extend(get_newforms(level, character=eps,
                                       algorithm=algorithm, path=path))
            done_levels.append((level, eps, Lbeta))
        return result
            
    def _repr_(self):
        """Give a string representation of a Frey Q-curve.

        .. NOTE::

        This is a direct copy from the code included
        in :class:`EllipticCurve_number_field`

        """
        b = self.ainvs()
        a = [z._coeff_repr() for z in b]
        s = "Frey Q-curve defined by "
        s += "y^2 "
        if a[0] == "-1":
            s += "- x*y "
        elif a[0] == '1':
            s += "+ x*y "
        elif b[0]:
            s += "+ %s*x*y "%a[0]
        if a[2] == "-1":
            s += "- y "
        elif a[2] == '1':
            s += "+ y "
        elif b[2]:
            s += "+ %s*y "%a[2]
        s += "= x^3 "
        if a[1] == "-1":
            s += "- x^2 "
        elif a[1] == '1':
            s += "+ x^2 "
        elif b[1]:
            s += "+ %s*x^2 "%a[1]
        if a[3] == "-1":
            s += "- x "
        elif a[3] == '1':
            s += "+ x "
        elif b[3]:
            s += "+ %s*x "%a[3]
        if a[4] == '-1':
            s += "- 1 "
        elif a[4] == '1':
            s += "+ 1 "
        elif b[4]:
            s += "+ %s "%a[4]
        s = s.replace("+ -","- ")
        s += "over %s "%(self.definition_field(),)
        s += "with parameters %s"%(self.parameters(),)
        return s
