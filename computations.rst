=======================================================
 On the equation :math:`(x-y)^4 + x^4 + (x+y)^4 = z^n`
=======================================================

In this document we give all the computations done for the paper.

.. linkall

Throughout :math:`(a, b, c)` will be a primitive solution to
:math:`(x-y)^4 + x^4 + (x+y)^4 = z^l` with :math:`l` a prime
number. We will also use the variable ``cl`` to denote :math:`c^l`.

::

   sage: load('load.sage')
   sage: R.<a, b> = ZZ[]
   sage: cl = (a-b)^4 + a^4 + (a+b)^4; cl
   3*a^4 + 12*a^2*b^2 + 2*b^4
   sage: coprime = CoprimeCondition([a, b])
   sage: con = coprime & PowerCondition(cl, 3)

Preliminaries
=============

We first check that Proposition 2.1 is indeed correct.

::

   sage: all(cl(aa, bb) != 0 for aa, bb in Integers(4)^2 if not 2.divides(aa) or not 2.divides(bb))
   True
   sage: all(cl(aa, bb) != 0 for aa, bb in Integers(9)^2 if not 3.divides(aa) or not 3.divides(bb))
   True
   sage: all(cl(aa, bb) != 0 for aa, bb in GF(5)^2 if (aa, bb) != (0, 0))
   True

Next we factor the polynomial ``cl`` as mentioned in the article over
the splitting field of :math:`3 x^4 + 12 x^2 + 2`. We also let
:math:`v` be a root of this polynomial and construct the polynomial
:math:`h`.

::

   sage: S.<x> = QQ[]
   sage: L.<vg> = cl(x, 1).splitting_field()
   sage: v = cl(x, 1).change_ring(L).roots()[0][0]
   sage: h = a + v*b

We verify that ``cl`` factors as in equation (5) and that the factors
are indeed galois conjugates of :math:`h`.

::

   sage: h1 = a - v*b
   sage: h2 = a + sqrt(-v^2 - 4)*b
   sage: h3 = a - sqrt(-v^2 - 4)*b
   sage: cl == 3 * h * h1 * h2 * h3
   True
   sage: G = L.galois_group()
   sage: h1 == h.change_ring(G[3].as_hom())
   True
   sage: h2 == h.change_ring(G[2].as_hom())
   True
   sage: h3 == h.change_ring(G[1].as_hom())
   True

We now perform the computations necessary for Lemma 2.2, i.e. we check
there is a unique prime ``P3`` above 3 in :math:`L`, that :math:`v` is
only not integral at ``P3`` and has valuation -1 there, and that the
difference between galois conjugates of :math:`v` only contain primes
above 2, 3 and 5. Note that we also use the fact that ``P3`` to the
power 4 is 3, which we also verify here.

::

   sage: len(L.primes_above(3)) == 1
   True
   sage: P3 = L.prime_above(3)
   sage: P235 = L.primes_above(2*3*5)
   sage: all(P in P235 for P, e in L.ideal(v).factor())
   True
   sage: [(P, e) for P, e in L.ideal(v).factor() if e < 0] == [(P3, -1)]
   True
   sage: all(P in P235
   ....:     for sigma, tau in [(sigma, tau) for sigma in G for tau in G if sigma(v) != tau(v)]
   ....:     for P, e in L.ideal(sigma(v) - tau(v)).factor())
   True
   sage: P3^4 == L.ideal(3)
   True

We check that over the subfield :math:`K = \QQ(\sqrt{30})` of
:math:`L` the polynomial ``cl`` factors as in equation (8), and that
both factors are indeed the product of two galois conjugates of
:math:`h`.

::

   sage: K.<w> = L.subfield(-sqrt(L(30)), name='w')[0]
   sage: g1 = a^2 + (2 + w/3)*b^2
   sage: g2 = a^2 + (2 - w/3)*b^2
   sage: cl == 3 * g1 * g2
   True
   sage: g1 == h * h1
   True
   sage: g2 == h2 * h3
   True

We check that indeed :math:`K` has a unique prime ``Q3`` above 3 and
that it factors as the square of ``P3`` in :math:`L`.

::

   sage: len(K.primes_above(3)) == 1
   True
   sage: Q3 = K.prime_above(3)
   sage: L.ideal(Q3) == P3^2
   True

Solving for small :math:`l`
===========================

Case :math:`l = 2`
------------------

We check there is indeed no primitive solution for :math:`l = 2`,
by checking all possibilities modulo 9.

::

   sage: all(cl(aa, bb) != cc^2 for aa, bb, cc in Integers(9)^3
   ....:     if not 3.divides(aa) or not 3.divides(bb))
   True

Case :math:`l = 3`
------------------

We first verify that :math:`K = \Q(\sqrt{30})` has class number 2 and
that ``Q3^(-4)`` is :math:`1/9`.

::

   sage: K.class_number()
   2
   sage: Q3^(-4)
   Fractional ideal (1/9)
   
We verify that the unit group of :math:`K` indeed has the structure
described in the article and name the generators accordingly.

::

   sage: K.unit_group()
   Unit group with structure C2 x Z of Number Field in w with defining polynomial x^2 - 30
   sage: u0, u1 = K.unit_group().gens_values()

Next we check that the ideal in K above 3 has an integral basis given
by 3 times the coefficients of :math:`g_1`.

::

   sage: BQ3 = [3*cf for cf in g1.coefficients()]; BQ3
   [3, w + 6]
   sage: Q3.integral_basis()
   [3, w]

Now we compute the formulas given in equation (9) for each possible
choice of :math:`j` and check they match the given description.

::

   sage: R2.<s, t> = QQ[]
   sage: gamma = sum(3 * cf * Rgen for cf, Rgen in zip(g1.coefficients(), R2.gens()))
   sage: vals = [1/9 * u1^j * gamma^3 for j in range(3)]
   sage: B = g1.coefficients()
   sage: valsB = [polynomial_split_on_basis(poly, B) for poly in vals]
   sage: F, G = zip(*valsB)
   sage: [(Fj.degree(), Fj.is_homogeneous()) for Fj in F]
   [(3, True), (3, True), (3, True)]
   sage: [(Gj.degree(), Gj.is_homogeneous()) for Gj in G]
   [(3, True), (3, True), (3, True)]
   sage: K.galois_group().gen()(u1) == u1^(-1)
   True
   sage: 1/3*gamma*gamma.change_ring(K.galois_group().gen().as_hom())
   3*s^2 + 12*s*t + 2*t^2
   
As discussed in the article we construct the corresponding
hyperelliptic curves.

::

   sage: FG = [F[j] * G[j] for j in range(3)]
   sage: C_magma = [magma.HyperellipticCurve(poly(x, 1)) for poly in FG]
   sage: C_magma
   [Hyperelliptic Curve defined by y^2 = 27*x^5 + 108*x^4 + 84*x^3 - 288*x^2 - 564*x - 368 over Rational Field,
     Hyperelliptic Curve defined by y^2 = -1242*x^6 - 1269*x^5 - 432*x^4 + 84*x^3 + 72*x^2 + 12*x over Rational Field,
     Hyperelliptic Curve defined by y^2 = -599940*x^6 - 627237*x^5 - 273132*x^4 - 63276*x^3 - 8208*x^2 - 564*x - 16 over Rational Field]

We verify that the curve for :math:`j = 2` has no local point on
:math:`\Q_3`.

::

   sage: C_magma[2].IsLocallySolvable(3)
   false
   
We show that the Jacobian for the curve :math:`C_0` has only
two-torsion points and only 2 of them.

::

   sage: C = C_magma[0]
   sage: J = C.Jacobian()
   sage: J.RankBound()
   0
   sage: J.TorsionBound(10)
   4
   sage: C.BadPrimes()
   [ 2, 3, 5 ]
   sage: C.ChangeRing(GF(7)).Jacobian()
   Jacobian of Hyperelliptic Curve defined by y^2 = 6*x^5 + 3*x^4 + 6*x^2 + 3*x + 3 over GF(7)
   sage: C.ChangeRing(GF(7)).Jacobian().AbelianGroup()
   Abelian Group isomorphic to Z/6 + Z/6
   Defined on 2 generators
   Relations:
   6*$.1 = 0
   6*$.2 = 0
   sage: J.TwoTorsionSubgroup()
   Abelian Group isomorphic to Z/2
   Defined on 1 generator
   Relations:
   2*P[1] = 0

Next we factor ``FG[0]`` to show the claim that :math:`t` is the only
linear factor.

::

   sage: FG[0].factor()
   t * (9*s^2 + 36*s*t + 46*t^2) * (3*s^3 - 6*s*t^2 - 8*t^3)

We now make the equations for the case :math:`j = 1` explicit to
verify the ones given in the article.

::

   sage: F[1].factor()
   (-3) * s * (23*s^2 + 12*s*t + 2*t^2)
   sage: G[1].factor()
   18*s^3 + 9*s^2*t - 2*t^3
   sage: 1/3 * gamma * gamma.change_ring(K.galois_group().gen().as_hom())
   3*s^2 + 12*s*t + 2*t^2

We verify that :math:`23 s^2 + 12 s t + 2 t^2` splits over
:math:`\Q(\sqrt{-10})` as mentioned in the article.

::

   sage: Qm10.<sqrtm10> = QuadraticField(-10)
   sage: beta = 3 + sqrtm10 / 2
   sage: beta_bar = Qm10.galois_group().gen()(beta)
   sage: 2 * (beta*s + t) * (beta_bar*s + t)
   23*s^2 + 12*s*t + 2*t^2

Next we check the last few details for the case :math:`l=3`.  The
unique prime above 3 in :math:`\Q(\sqrt{-10})` has norm 9.

::

   sage: len(Qm10.primes_above(3))
   1
   sage: Qm10.prime_above(3).norm()
   9

:math:`\beta` minus its conjugate is :math:`\sqrt{-10}`.

::

   sage: beta - beta_bar
   sqrtm10

The unique prime above 2 in :math:`\Q(\sqrt{-10})` is not principal.

::

   sage: len(Qm10.primes_above(2))
   1
   sage: Qm10.prime_above(2).is_principal()
   False

The field :math:`\Q(\sqrt{-10})` has class number 2

::

   sage: Qm10.class_number()
   2

Case :math:`l = 5`
------------------

We first check that ``P3^4`` is the principal ideal :math:`(3)` and
that 5 does not divide the order of the class group of :math:`L`.

::

   sage: P3^4
   Fractional ideal (3)
   sage: 5.divides(L.class_number())
   False

Next we check that the arguments given hold true if we replace
:math:`L` with the subfield :math:`\QQ(v)`. Since :math:`h` can be
defined over this subfield all we have to check is that the prime
above 3 in :math:`\QQ(v)` factors as ``P3`` in :math:`L` and that 5
again does not divide the order of the class group.

::

   sage: Qv = L.subfield(v, names='v')[0]
   sage: L.ideal(Qv.prime_above(3)) == P3
   True
   sage: 5.divides(Qv.class_number())
   False

We quickly verify that :math:`\QQ(v)` has degree 4 and parametrize the
elements of its ring of integers.

::

   sage: Qv.degree()
   4
   sage: R4.<s1, s2, s3, s4> = QQ[]
   sage: gamma = 1/3 * sum(product(term) for term in zip(R4.gens(), Qv.integral_basis()))

We check that the unit group of :math:`\QQ(v)` is indeed generated by
two generators ``u0`` and ``u1``, where ``u0`` = -1 and ``u1`` has
infinite order.

::

   sage: len(Qv.unit_group().gens())
   2
   sage: u0, u1 = Qv.unit_group().gens_values()
   sage: u0 == -1
   True
   sage: u1.multiplicative_order()
   +Infinity

We now generate the possible values of :math:`h(a, b)` inside
:math:`\QQ(v)`.

::

   sage: vals = [3 * u1^i * gamma^5 for i in range(5)]

Now we express each of these values in terms of the basis :math:`( 1,
v, v^2, v^3 )`.

::

   sage: B = [Qv(1), Qv(v), Qv(v)^2, Qv(v)^3]
   sage: valsB = [polynomial_split_on_basis(val, B) for val in vals]

Since each value is equal to :math:`h(a, b) = a + b v + 0 v^2 + 0 v^3`
with :math:`a` and :math:`b` integers we obtain for each i four
equations ``a == valsB[i][0]``, ``b == valsB[i][1]``, ``0 ==
valsB[i][2]`` and ``0 == valsB[i][3]`` over the rationals. We show
that these equations are actually integral except at 3.

::

   sage: all(p == 3 for valB in valsB for poly in valB for cf in poly.coefficients()
   ....:     for p in cf.denominator().prime_factors())
   True

This implies that we can consider the equations modulo 5. Now for each
choice of value of :math:`h(a, b)` we can express the value of the
tuple :math:`(a, b)` in a special way using the equations.

::

   sage: valsB5 = [[poly.change_ring(GF(5)) for poly in valB] for valB in valsB]
   sage: (valsB5[0][0],                 valsB5[0][1] -  valsB5[0][3])
   (s1^5 - s3^5, 0)
   sage: (valsB5[1][0] -  valsB5[1][2], valsB5[1][1] +  valsB5[1][3])
   (0, 0)
   sage: (valsB5[2][0] +  valsB5[2][2], valsB5[2][1])
   (0, 0)
   sage: (valsB5[3][0],                 valsB5[3][1] +2*valsB5[3][3])
   (0, 0)
   sage: (valsB5[4][0] +2*valsB5[4][2], valsB5[4][1] +  valsB5[4][3])
   (0, 2*s2^5 + s4^5)

This shows that in three of the five cases both :math:`a` and
:math:`b` must be divisible by 5, but as :math:`a` and :math:`b` are
coprime this is impossible. We are thus left with case 0 and case 4 as
stated in the article.

We take the automorphism :math:`\sigma` of :math:`\QQ(v)` that sends
:math:`v` to :math:`-v` and check that ``g1`` is indeed the product of
:math:`h` and :math:`\sigma(h)`.

::

   sage: sigma = Qv.hom([-Qv(v)])
   sage: g1 == h.change_ring(Qv) * h.change_ring(Qv).change_ring(sigma)
   True

We will construct the parametrizations as described in the article for
the remaining cases. First we parametrize what is called
:math:`\gamma'` and what we shall call ``gamma`` again here.

::

   sage: K.degree()
   2
   sage: R2.<s, t> = QQ[]
   sage: gamma = sum(product(term) for term in zip(R2.gens(), [1, w/3]))

Next we find the possible values for :math:`g_1(a, b)`. Note that we
here only have to consider those units not eliminated by the argument
before.

::

   sage: vals = [9 * K(u1^i * sigma(u1^i)) * gamma^5 for i in [0, 4]]

Next we write each value in terms of the basis given by the
coefficients of ``g1``.

::

   sage: B = g1.coefficients()
   sage: valsB = [polynomial_split_on_basis(val, B) for val in vals]

We verify the validity of equation (10). Note that to compute the
formula for :math:`c` we need that the conjugate of :math:`u'` is its
inverse in each case.
   
::

   sage: F, G = zip(*valsB)
   sage: [Fj.degree() for Fj in F]
   [5, 5]
   sage: [Gj.degree() for Gj in G]
   [5, 5]
   sage: K.galois_group().gen()(K(u1 * sigma(u1))) == K(u1 * sigma(u1))^(-1)
   True
   sage: 3 * gamma * gamma.change_ring(K.galois_group().gen().as_hom())
   3*s^2 - 10*t^2

We construct the hyperelliptic curves described in the article.
::

   sage: FG = [F[j] * G[j] for j in range(len(F))]
   sage: C_magma = [magma.HyperellipticCurve(poly(x, 1)) for poly in FG]
   sage: C_magma
   [Hyperelliptic Curve defined by y^2 = 405*x^9 - 4050*x^8 + 16200*x^7 - 54000*x^6 + 113400*x^5 - 198000*x^4 + 180000*x^3 - 120000*x^2 + 50000*x - 20000 over Rational Field,
    Hyperelliptic Curve defined by y^2 = -3083903014930297409520*x^10 - 56304108214517165808555*x^9 - 462585452239544611432050*x^8 - 2252164328580686632342200*x^7 - 7195773701504027288934000*x^6 - 15765150300064806426395400*x^5 - 23985912338346757629798000*x^4 - 25024048095340962581580000*x^3 - 17132794527390541164120000*x^2 - 6951124470928045161550000*x - 1269095890917817864020000 over Rational Field]

We analyze the Jacobians of these curves to see that the only rational
points on them are two-torsion points and there are only two such
points.

::

   sage: J_magma = [C.Jacobian() for C in C_magma]
   sage: [J.RankBound() for J in J_magma]
   [0, 0]
   sage: [J.TorsionBound(50) for J in J_magma]
   [4, 4]
   sage: all(7 not in C.BadPrimes().sage() for C in C_magma)
   True
   sage: J7 = [C.ChangeRing(GF(7)).Jacobian() for C in C_magma]
   sage: all(not 4.divides(g.Order()) for J in J7 for g in J.AbelianGroup().Generators())
   True

We compute the factors of the product :math:`F G`.

::

   sage: [poly.factor() for poly in FG]
   [(5) * t * (9*s^4 + 60*s^2*t^2 + 20*t^4) * (9*s^5 - 90*s^4*t + 300*s^3*t^2 - 600*s^2*t^3 + 500*s*t^4 - 200*t^5),
    (-5) * (23*s + 42*t) * (201580749*s^4 + 1472068080*s^3*t + 4031233980*s^2*t^2 + 4906429920*s*t^3 + 2239362820*t^4) * (133031294352*s^5 + 1214404012845*s^4*t + 4434376478400*s^3*t^2 + 8096026752300*s^2*t^3 + 7390627464000*s*t^4 + 2698675584100*t^5)]

Lastly we check that the linear factors above indeed give :math:`c`
divisible by 2 or 3.

::

   sage: (3 * gamma * gamma.change_ring(K.galois_group().gen().as_hom()))(s, 0)
   3*s^2
   sage: (3 * gamma * gamma.change_ring(K.galois_group().gen().as_hom()))(42*s, -23*s)
   2*s^2
   
The Frey Curves
===============

First we check the mentioned fact. We take :math:`B_1` and :math:`A`
as variables and will set :math:`B_2 = A^2 - B_1`. We define the
elliptic curve as in section 4.

::

   sage: Rt.<A, B1> = QQ[]
   sage: B2 = A^2 - B1
   sage: E = EllipticCurve([0, 2*A, 0, B1, 0])

Next we check that the invariants are as mentioned

::

   sage: E.discriminant() == 64 * B1^2 * B2
   True
   sage: E.c4() == 16*(B1 + 4*B2)
   True

Next we check that we indeed have that the given linear combinations
of :math:`g_1(a, b)` and :math:`g_2(a, b)` are squares

::

   sage: (1/2 - w/10)*g1 + (1/2 + w/10)*g2 == a^2
   True
   sage: (w/20)*g1 - (w/20)*g2 == b^2
   True

Next we construct the four possible Frey curves that are constructed
from this as mentioned in the article, and also check that in each
pair the two curves are galois conjugates of one another.

::

   sage: E1_ = FreyCurve([0, 2*a, 0, (1/2 - w/10)*g1, 0], condition=con)
   sage: E1__ = FreyCurve([0, 2*a, 0, (1/2 + w/10)*g2, 0], condition=con)
   sage: E2_ = FreyCurve([0, 2*b, 0, (w/20)*g1, 0], condition=con)
   sage: E2__ = FreyCurve([0, 2*b, 0, -(w/20)*g2, 0], condition=con)
   sage: G.<sigma> = K.galois_group()
   sage: E1__.a_invariants() == E1_.change_ring(sigma.as_hom()).a_invariants()
   True
   sage: E2__.a_invariants() == E2_.change_ring(sigma.as_hom()).a_invariants()
   True

We choose the two elliptic curves :math:`E_1'` and :math:`E_2` as
mentioned and twist them by 30 and 20 respectively. We check that we
get the same curves as mentioned in the article.

::

   sage: E1 = FreyCurve(twist_elliptic_curve(E1__, 30), condition=con)
   sage: E2 = FreyCurve(twist_elliptic_curve(E2_, 20), condition=con)
   sage: E1.a_invariants() == (0, 60*a, 0, 30*((15 + 3*w)*a^2 + w*b^2), 0)
   True
   sage: E2.a_invariants() == (0, 40*b, 0, 20*(w*a^2 + (10 + 2*w)*b^2), 0)
   True

Next we check that all the mentioned invariants were computed correctly

::

   sage: E1.discriminant() == - 2^9 * 3^6 * 5^4 * (5 + w) * g1 * g2^2
   True
   sage: E2.discriminant() == - 2^13 * 3 * 5^4 * w * g1^2 * g2
   True
   sage: E1.c4() == - 2^5 * 3^2 * 5 * (5 + w) * ((43 - 8*w)*a^2 + (6 - w)*b^2)
   True
   sage: E2.c4() == - 2^6 * 3^(-1) * 5 * w * (9*a^2 + (18 - 5*w)*b^2)
   True
   sage: E1.j_invariant() == (11 + 2*w) * 2^6 * ((43 - 8*w)*a^2 + (6 - w)*b^2)^3 / (g1 * g2^2)
   True
   sage: E2.j_invariant() == 2^6 * 3^(-3) * (9*a^2 + (18 - 5*w)*b^2)^3 / (g1^2 * g2)
   True

We show that the resultants of :math:`g_1` and :math:`g_2` with the
factors in the numerators of :math:`j_1` and :math:`j_2` are indeed
only divisible by primes dividing 2, 3 or 5, affirming the statement
made in Lemma 4.1. For this we simply compute the prime factors in the
norm, which is sufficient as the numerators are integral and the only
prime at which :math:`g_1` and :math:`g_2` are not integral divides 3.

::

   sage: g1.macaulay_resultant((43 - 8*w)*a^2 + (6 - w)*b^2).norm().factor()
   2^6 * 3^-2 * 5^2
   sage: g1.macaulay_resultant(9*a^2 + (18 - 5*w)*b^2).norm().factor()
   2^14 * 3^2 * 5^2
   sage: g2.macaulay_resultant((43 - 8*w)*a^2 + (6 - w)*b^2).norm().factor()
   2^14 * 3^-2 * 5^2
   sage: g2.macaulay_resultant(9*a^2 + (18 - 5*w)*b^2).norm().factor()
   2^6 * 3^2 * 5^2

A Hilbert modular approach
==========================

We verify Proposition 5.1 by computing the conductors of both curves
and showing they are equal to the mentioned expression.

::

   sage: P2 = K.prime_above(2)
   sage: P3 = K.prime_above(3)
   sage: P5 = K.prime_above(5)
   sage: N1 = E1.conductor(); N1
   Warning: Assuming that a and b are coprime.
   (2, w)^n0*(3)*(5)*Rad_P( ((-233280000*w - 1166400000)) * (a^2 + (1/3*w + 2)*b^2) * (a^2 + (-1/3*w + 2)*b^2)^2 )
    where 
   n0 = 12 if ('a', 'b') == (1, 0) mod 2
        10 if ('a', 'b') == (1, 1) mod 2
   sage: N1.left().value()
   Fractional ideal (960) if ('a', 'b') == (1, 0) mod 2
   Fractional ideal (480) if ('a', 'b') == (1, 1) mod 2
   sage: N1.left().value()[0][0] == P2^12 * P3^2 * P5^2
   True
   sage: N1.left().value()[1][0] == P2^10 * P3^2 * P5^2
   True
   sage: N1.right() == "Rad_P( " + str(E1.discriminant().factor()) + " )"
   True
   sage: N2 = E2.conductor(); N2
   Warning: Assuming that a and b are coprime.
   (640)*Rad_P( ((-15360000*w)) * (a^2 + (-1/3*w + 2)*b^2) * (a^2 + (1/3*w + 2)*b^2)^2 )
   sage: N2.left() == P2^14 * P5^2
   True
   sage: N2.right() == "Rad_P( " + str(E2.discriminant().factor()) + " )"
   True

We perform the computations necessary to find a twist with smaller
conductor. First we test all possible twists that might lower the
level for the prime ``P2`` above 2. The group :math:`K^*/H` is in this
case generated by ``w``, -1, and ``1 + w``.

::

   sage: FreyCurve(twist_elliptic_curve(E1, 1), condition=con).conductor_exponent(P2)
   12 if ('a', 'b') == (1, 0) mod 2
   10 if ('a', 'b') == (1, 1) mod 2
   sage: FreyCurve(twist_elliptic_curve(E1, -1), condition=con).conductor_exponent(P2)
   12 if ('a', 'b') == (1, 0) mod 2
   10 if ('a', 'b') == (1, 1) mod 2
   sage: FreyCurve(twist_elliptic_curve(E1, w), condition=con).conductor_exponent(P2)
   12 if ('a', 'b') == (1, 0) mod 2
   8  if ('a', 'b') == (1, 1) mod 2
   sage: FreyCurve(twist_elliptic_curve(E1, -w), condition=con).conductor_exponent(P2)
   12 if ('a', 'b') == (1, 0) mod 2
   8  if ('a', 'b') == (1, 1) mod 2
   sage: FreyCurve(twist_elliptic_curve(E1, 1+w), condition=con).conductor_exponent(P2)
   12 if ('a', 'b') == (1, 0) mod 2
   10 if ('a', 'b') == (1, 1) mod 2
   sage: FreyCurve(twist_elliptic_curve(E1, -1-w), condition=con).conductor_exponent(P2)
   12 if ('a', 'b') == (1, 0) mod 2
   10 if ('a', 'b') == (1, 1) mod 2
   sage: FreyCurve(twist_elliptic_curve(E1, 30+w), condition=con).conductor_exponent(P2)
   12 if ('a', 'b') == (1, 0) mod 2
   0  if ('a', 'b') == (3, 1), (3, 3) mod 4
   4  if ('a', 'b') == (1, 1), (1, 3) mod 4
   sage: FreyCurve(twist_elliptic_curve(E1, -30-w), condition=con).conductor_exponent(P2)
   12 if ('a', 'b') == (1, 0) mod 2
   0  if ('a', 'b') == (1, 1), (1, 3) mod 4
   4  if ('a', 'b') == (3, 1), (3, 3) mod 4
   sage: FreyCurve(twist_elliptic_curve(E2, 1), condition=con).conductor_exponent(P2)
   14
   sage: FreyCurve(twist_elliptic_curve(E2, -1), condition=con).conductor_exponent(P2)
   14
   sage: FreyCurve(twist_elliptic_curve(E2, w), condition=con).conductor_exponent(P2)
   14
   sage: FreyCurve(twist_elliptic_curve(E2, -w), condition=con).conductor_exponent(P2)
   14
   sage: FreyCurve(twist_elliptic_curve(E2, 1+w), condition=con).conductor_exponent(P2)
   14
   sage: FreyCurve(twist_elliptic_curve(E2, -1-w), condition=con).conductor_exponent(P2)
   14
   sage: FreyCurve(twist_elliptic_curve(E2, 30+w), condition=con).conductor_exponent(P2)
   14
   sage: FreyCurve(twist_elliptic_curve(E2, -30-w), condition=con).conductor_exponent(P2)
   14

We see the best we can do at ``P2`` is as described in the remark.

Now for the prime ``P3`` above 3, the group :math:`K^*/H` is generated
by ``w``.

::
   
   sage: FreyCurve(twist_elliptic_curve(E1, 1), condition=con).conductor_exponent(P3)
   2
   sage: FreyCurve(twist_elliptic_curve(E1, w), condition=con).conductor_exponent(P3)
   2
   sage: FreyCurve(twist_elliptic_curve(E2, 1), condition=con).conductor_exponent(P3)
   0
   sage: FreyCurve(twist_elliptic_curve(E2, w), condition=con).conductor_exponent(P3)
   2

Again we see the best we can do at ``P3`` is as in the remark.

For the prime ``P5`` above 5 the group :math:`K^*/H` is generated by
``w``.

::

   sage: FreyCurve(twist_elliptic_curve(E1, 1), condition=con).conductor_exponent(P5)
   2
   sage: FreyCurve(twist_elliptic_curve(E1, w), condition=con).conductor_exponent(P5)
   2
   sage: FreyCurve(twist_elliptic_curve(E2, 1), condition=con).conductor_exponent(P5)
   2
   sage: FreyCurve(twist_elliptic_curve(E2, w), condition=con).conductor_exponent(P5)
   2

So again the level in the remark is the best we can do at ``P5``.

Lastly we check that the twists mentioned in the remark give the
desired levels.

::

   sage: FreyCurve(twist_elliptic_curve(E1, 6+w), condition=con).conductor()
   Warning: Assuming that a and b are coprime.
   (2, w)^n0*(3)*(5)*Rad_P( ((-509981806080000*w - 2793285388800000)) * (a^2 + (1/3*w + 2)*b^2) * (a^2 + (-1/3*w + 2)*b^2)^2 )
    where 
   n0 = 12 if ('a', 'b') == (1, 0) mod 2
        0  if ('a', 'b') == (3, 1), (3, 3) mod 4
        4  if ('a', 'b') == (1, 1), (1, 3) mod 4
   sage: FreyCurve(twist_elliptic_curve(E1, -6-w), condition=con).conductor()
   Warning: Assuming that a and b are coprime.
   (2, w)^n0*(3)*(5)*Rad_P( ((-509981806080000*w - 2793285388800000)) * (a^2 + (1/3*w + 2)*b^2) * (a^2 + (-1/3*w + 2)*b^2)^2 )
    where 
   n0 = 12 if ('a', 'b') == (1, 0) mod 2
        0  if ('a', 'b') == (1, 1), (1, 3) mod 4
        4  if ('a', 'b') == (3, 1), (3, 3) mod 4

We compute the dimensions of the spaces of Hilbert modular forms
mentioned in the article for the levels given.

::

   sage: magma.HilbertCuspForms(K, N1.left().value()[0][0]).NewSubspace().Dimension()
   826880
   sage: magma.HilbertCuspForms(K, N1.left().value()[1][0]).NewSubspace().Dimension()
   206720
   sage: magma.HilbertCuspForms(K, N2.left()).NewSubspace().Dimension()
   661504
   sage: magma.HilbertCuspForms(K, P3^2*P5^2).NewSubspace().Dimension()
   542

Q-curves
========
   
We turn our two curves into :math:`\QQ` curves.
   
::

   sage: Qm2.<sqrtm2> = QuadraticField(-2)
   sage: G.<sigma> = K.galois_group()
   sage: isogenies = {sigma^0: (QQ(1), 1), sigma^1: (sqrtm2, 2)}
   sage: E1 = FreyQcurve(E1, isogenies=isogenies, condition=con)
   sage: E2 = FreyQcurve(E2, isogenies=isogenies, condition=con)

Basic invariants
----------------

We compute all the data mentioned in Proposition 6.2. First of all the
degree map.

::

   sage: [E1.degree_map(s) for s in G]
   [1, 2]
   sage: [E2.degree_map(s) for s in G]
   [1, 2]

Second the 2-cocyle :math:`c`.
   
::
   
   sage: Kcomp = E1.complete_definition_field()
   sage: ls = list(Kcomp.galois_group())
   sage: [s(sqrt(Kcomp(-2))) / sqrt(Kcomp(-2)) for s in ls]
   [1, 1, -1, -1]
   sage: [s(sqrt(Kcomp(30))) / sqrt(Kcomp(30)) for s in ls]
   [1, -1, 1, -1]
   sage: matrix([[E1.c(s, t) for t in ls] for s in ls])
   [ 1  1  1  1]
   [ 1 -2  1 -2]
   [ 1 -1  1 -1]
   [ 1  2  1  2]
   sage: matrix([[E2.c(s, t) for t in ls] for s in ls])
   [ 1  1  1  1]
   [ 1 -2  1 -2]
   [ 1 -1  1 -1]
   [ 1  2  1  2]
   
Next the definition field and the complete definition field.

::
   
   sage: E1.definition_field().is_isomorphic(QQ[sqrt(30)])
   True
   sage: E2.definition_field().is_isomorphic(QQ[sqrt(30)])
   True
   sage: E1.complete_definition_field().is_isomorphic(QQ[sqrt(30),sqrt(-2)])
   True
   sage: E2.complete_definition_field().is_isomorphic(QQ[sqrt(30),sqrt(-2)])
   True

Next the dual basis.

::

   sage: E1.dual_basis()
   ([30], [2])
   sage: E2.dual_basis()
   ([30], [2])

Lastly a splitting character and the corresponding fields.

::

   sage: E1.splitting_character()
   Dirichlet character modulo 15 of conductor 15 mapping 11 |--> -1, 7 |--> zeta4
   sage: E2.splitting_character()
   Dirichlet character modulo 15 of conductor 15 mapping 11 |--> -1, 7 |--> zeta4
   sage: L15.<zeta15> = CyclotomicField(15)
   sage: Keps = L15.subfield(zeta15 + zeta15^(-1))[0]
   sage: E1.splitting_character_field().is_isomorphic(Keps)
   True
   sage: E2.splitting_character_field().is_isomorphic(Keps)
   True
   sage: Keps.degree()
   4
   sage: Kbeta = composite_field(K, Keps)
   sage: E1.splitting_field().is_isomorphic(Kbeta)
   True
   sage: E2.splitting_field().is_isomorphic(Kbeta)
   True
   sage: Kbeta.degree()
   8
   sage: Kdec = composite_field(QQ[sqrt(-2), sqrt(-3)], Keps)
   sage: E1.decomposition_field().is_isomorphic(Kdec)
   True
   sage: E2.decomposition_field().is_isomorphic(Kdec)
   True
   sage: Kdec.degree()
   16

Finally we verify the inequalities in the remark at the end of this
subsection.

::

   sage: hilbert_symbol(30, 2, 5) != 1
   True
   sage: hilbert_symbol(30, 2, 5) != hilbert_symbol(-1, 30, 5)
   True

A decomposable twist
--------------------

First we compute that the class number of ``Kdec`` is indeed 1.

::

   sage: Kdec.class_number()
   1

Using the code we can directly compute a twist for which the
restriction of scalars decomposes. We compute that the twist factor of
these curves both differs differ by a square from the :math:`\gamma`
given in the article.

::

   sage: f_gamma = x^8 - 40*x^7 - 550*x^6 - 1840*x^5 - 285*x^4 + 3600*x^3 - 1950*x^2 + 200*x + 25
   sage: gamma = f_gamma.change_ring(Kdec).roots()[0][0]
   sage: iota = K.embeddings(E1.decomposition_field())[0]
   sage: E1t = E1.decomposable_twist()
   sage: ((E1t.a2() / E1.a2().change_ring(iota)).numerator().constant_coefficient()
   ....:   / Kdec.embeddings(E1.decomposition_field())[0](gamma)).is_square()
   True
   sage: E2t = E2.decomposable_twist()
   sage: ((E2t.a2() / E2.a2().change_ring(iota)).numerator().constant_coefficient()
   ....:   / Kdec.embeddings(E2.decomposition_field())[0](gamma)).is_square()
   True

Since we work with the twists by :math:`\gamma` we define those twists
and check that the restriction of scalars indeed decomposes, as
claimed in Proposition 6.3.

::

   sage: E1c = E1.twist(gamma)
   sage: E1c.does_decompose()
   True
   sage: E2c = E2.twist(gamma)
   sage: E2c.does_decompose()
   True

As remarked in the article we verify that some of the fields associated
to the twisted curve are indeed different.

::

   sage: E1c.definition_field().is_isomorphic(Kdec.subfield(gamma)[0])
   True
   sage: E2c.definition_field().is_isomorphic(Kdec.subfield(gamma)[0])
   True
   sage: E1c.complete_definition_field().is_isomorphic(Kdec.subfield(gamma)[0])
   True
   sage: E2c.complete_definition_field().is_isomorphic(Kdec.subfield(gamma)[0])
   True
   sage: E1c.splitting_character_field().is_isomorphic(Keps)
   True
   sage: E2c.splitting_character_field().is_isomorphic(Keps)
   True
   sage: E1c.splitting_field().is_isomorphic(Kbeta)
   True
   sage: E2c.splitting_field().is_isomorphic(Kbeta)
   True
   sage: E1c.decomposition_field().is_isomorphic(Kdec.subfield(gamma)[0])
   True
   sage: E2c.decomposition_field().is_isomorphic(Kdec.subfield(gamma)[0])
   True
   sage: Kbeta.is_isomorphic(Kdec.subfield(gamma)[0])
   True

We compute the last data needed to prove Theorem 6.4. That is we
compute the image fields of one splitting map in each galois conjugacy
class of splitting maps. This tells us that the decomposition is as
mentioned in the article.

::

   sage: E1c.splitting_image_field('conjugacy')
   (Cyclotomic Field of order 8 and degree 4,
    Cyclotomic Field of order 8 and degree 4)
   sage: E2c.splitting_image_field('conjugacy')
   (Cyclotomic Field of order 8 and degree 4,
    Cyclotomic Field of order 8 and degree 4)

Modularity of Q-curves
----------------------

For Theorem 6.6 we first compute a splitting character for each
conjugacy class, giving us the characters for the newforms

::

   sage: E1c.splitting_character('conjugacy')
   (Dirichlet character modulo 15 of conductor 15 mapping 11 |--> -1, 7 |--> zeta4,
    Dirichlet character modulo 15 of conductor 15 mapping 11 |--> -1, 7 |--> -zeta4)
   sage: E2c.splitting_character('conjugacy')
   (Dirichlet character modulo 15 of conductor 15 mapping 11 |--> -1, 7 |--> zeta4,
    Dirichlet character modulo 15 of conductor 15 mapping 11 |--> -1, 7 |--> -zeta4)

Next we compute the conductors of the restriction of scalar as
mentioned in the proof.

::

   sage: N1 = E1c.conductor_restriction_of_scalars(); N1
   Warning: Assuming that a and b are coprime.
   2^(4*n0+24)*43046721*244140625*Norm(Rad_P( ((23782266551879220937500/59141881469*azeta1500^7 + 1126822572008348510812500/59141881469*azeta1500^6 + 13988031177932864349750000/59141881469*azeta1500^5 - 59265495307535319274500000/59141881469*azeta1500^4 - 1775371096351391663808000000/59141881469*azeta1500^3 - 1236605090022138111120000000/59141881469*azeta1500^2 + 58326576546407013852786000000/59141881469*azeta1500 + 6699553759806124820472000000/59141881469)) * (a^2 + (1/1001088*azeta1500^7 + 1/111232*azeta1500^6 - 21/27808*azeta1500^5 - 1163/125136*azeta1500^4 + 249/3476*azeta1500^3 + 578/869*azeta1500^2 - 111719/31284*azeta1500 + 8884/2607)*b^2) * (a^2 + (-1/1001088*azeta1500^7 - 1/111232*azeta1500^6 + 21/27808*azeta1500^5 + 1163/125136*azeta1500^4 - 249/3476*azeta1500^3 - 578/869*azeta1500^2 + 111719/31284*azeta1500 + 1544/2607)*b^2)^2 ))
    where 
   n0 = 12 if ('a', 'b') == (1, 0) mod 2
        10 if ('a', 'b') == (1, 1) mod 2
   sage: N2 = E2c.conductor_restriction_of_scalars(); N2
   Warning: Assuming that a and b are coprime.
   1936465405881733890441216000000000000*Norm(Rad_P( ((17973045129994189000000/59141881469*azeta1500^7 + 851560867877408703000000/59141881469*azeta1500^6 + 10570632468562506924000000/59141881469*azeta1500^5 - 44792083812043020808000000/59141881469*azeta1500^4 - 1341640897948993214880000000/59141881469*azeta1500^3 - 934184557863352113984000000/59141881469*azeta1500^2 + 44076529752976112634848000000/59141881469*azeta1500 + 5062815140007181381632000000/59141881469)) * (a^2 + (-1/1001088*azeta1500^7 - 1/111232*azeta1500^6 + 21/27808*azeta1500^5 + 1163/125136*azeta1500^4 - 249/3476*azeta1500^3 - 578/869*azeta1500^2 + 111719/31284*azeta1500 + 1544/2607)*b^2) * (a^2 + (1/1001088*azeta1500^7 + 1/111232*azeta1500^6 - 21/27808*azeta1500^5 - 1163/125136*azeta1500^4 + 249/3476*azeta1500^3 + 578/869*azeta1500^2 - 111719/31284*azeta1500 + 8884/2607)*b^2)^2 ))

We check that this is indeed the same as the expression given in the
proof of Proposition 4.9. For the left side this is an easy check.

::

   sage: N1.left().value()
   49629490343711156465565696000000000000 if ('a', 'b') == (1, 0) mod 2
   193865196655121704943616000000000000   if ('a', 'b') == (1, 1) mod 2
   sage: N1.left().value()[0][0] == 2^72 * 3^16 * 5^12
   True
   sage: N1.left().value()[1][0] == 2^64 * 3^16 * 5^12
   True
   sage: N2.left() == 2^80 * 3^8 * 5^12
   True

For the right side we first note that this is the norm of the radical
of the discriminant outside primes dividing 30.

::

   sage: N1.right() == "Norm(Rad_P( " + str(E1c.discriminant().factor()) + " ))"
   True
   sage: N2.right() == "Norm(Rad_P( " + str(E2c.discriminant().factor()) + " ))"
   True
   sage: (Set(E1c.primes_of_possible_additive_reduction()) ==
   ....:  Set(E1c.definition_field().primes_above(30)))
   True
   sage: (Set(E2c.primes_of_possible_additive_reduction()) ==
   ....:  Set(E2c.definition_field().primes_above(30)))
   True

Next we note that these discriminants are just a product of
:math:`g_1(a, b)`, :math:`g_2(a, b)` and an integral number only
divisible by primes dividing 30.

::

   sage: iota = K.embeddings(E1c.decomposition_field())[0]
   sage: cf = E1c.discriminant() / (g1.change_ring(iota) * g2.change_ring(iota)^2); cf
   (23782266551879220937500/59141881469*azeta1500^7 + 1126822572008348510812500/59141881469*azeta1500^6 + 13988031177932864349750000/59141881469*azeta1500^5 - 59265495307535319274500000/59141881469*azeta1500^4 - 1775371096351391663808000000/59141881469*azeta1500^3 - 1236605090022138111120000000/59141881469*azeta1500^2 + 58326576546407013852786000000/59141881469*azeta1500 + 6699553759806124820472000000/59141881469)
   sage: cf = cf.numerator().constant_coefficient()
   sage: cf.is_integral()
   True
   sage: cf.norm().factor()
   2^72 * 3^48 * 5^48
   sage: cf = E2c.discriminant() / (g1.change_ring(iota)^2 * g2.change_ring(iota)); cf
   (17973045129994189000000/59141881469*azeta1500^7 + 851560867877408703000000/59141881469*azeta1500^6 + 10570632468562506924000000/59141881469*azeta1500^5 - 44792083812043020808000000/59141881469*azeta1500^4 - 1341640897948993214880000000/59141881469*azeta1500^3 - 934184557863352113984000000/59141881469*azeta1500^2 + 44076529752976112634848000000/59141881469*azeta1500 + 5062815140007181381632000000/59141881469)
   sage: cf = cf.numerator().constant_coefficient()
   sage: cf.is_integral()
   True
   sage: cf.norm().factor()
   2^108 * 3^12 * 5^48

This implies that the right side is just the norm of the radical of
:math:`c` outside primes dividing 30. Since the field :math:`K_\beta`
only ramifies at primes dividing 30 and has degree 8, we easily find
that this is simply the radical of :math:`c` over the integers outside
30, to the power 8. We verify that only the primes dividing 30 ramify
and that the degree of :math:`K_\beta` is 8 here.

::

   sage: Kbeta.discriminant().factor()
   2^12 * 3^4 * 5^6
   sage: Kbeta.degree()
   8

To verify the rest of the proof we compute the twists between the
newforms. These are the same as the inverses of the twists between the
corresponding splitting maps which we can compute with respect to the
splitting map computed first.

::

   sage: E1c.twist_character('conjugacy')
   (Dirichlet character modulo 120 of conductor 1 mapping 31 |--> 1, 61 |--> 1, 41 |--> 1, 97 |--> 1,
    Dirichlet character modulo 120 of conductor 40 mapping 31 |--> -1, 61 |--> -1, 41 |--> 1, 97 |--> zeta4)
   sage: E2c.twist_character('conjugacy')
   (Dirichlet character modulo 120 of conductor 1 mapping 31 |--> 1, 61 |--> 1, 41 |--> 1, 97 |--> 1,
    Dirichlet character modulo 120 of conductor 40 mapping 31 |--> -1, 61 |--> -1, 41 |--> 1, 97 |--> zeta4)

We verify that the inverse of the second character in each case is
indeed :math:`\varepsilon_8 \varepsilon_5`, implying the remainder of
the proof to be valid.

::

   sage: chi = E1c.twist_character('conjugacy')[1]^(-1)
   sage: eps8 = [eps for eps in DirichletGroup(8) if eps.conductor() == 8 and eps(-1) == -1][0]
   sage: eps5 = [eps for eps in DirichletGroup(5) if eps.order() == 4][1]
   sage: chi == eps8.extend(120) * eps5.extend(120)
   True

Level lowering
--------------
    
We now perform the computational part of Theorem 6.7. We check for
:math:`l = 7, 13` that the curve :math:`X_0(2l)` has no :math:`K`
point corresponding to a :math:`\QQ` point on :math:`X_0(2l) / w_2`.

We start with the case :math:`l = 7`, in which the modular curve is an
elliptic curve.

::

   sage: _ = magma.eval("X14 := SmallModularCurve(14);")
   sage: _ = magma.eval("w2 := AtkinLehnerInvolution(X14, 14, 2);")
   sage: print(magma.eval("Genus(X14);"))
   1

The morphism :math:`w_2` is a combination of an isogeny with a
translation. Since :math:`w_2` is an isomorphism, the isogeny must be
an isomorphism as well and :math:`w_2` is essentially defined as a
translation, which is given by where :math:`w2` maps the point at
infinity. We use this to compute the quotient :math:`X_0(14) / w_2` as
the quotient of the curve by the subgroup generated by this point. We
show this is an elliptic curve with 6 :math:`\QQ` points.

::

   sage: _ = magma.eval("P := w2(X14 ! [0, 1, 0]);")
   sage: _ = magma.eval("phi := TwoIsogeny(P);")
   sage: _ = magma.eval("X14modW2 := Codomain(phi);")
   sage: print(magma.eval("Genus(X14modW2)"))
   1
   sage: print(magma.eval("AbelianGroup(X14modW2)"))
   Abelian Group isomorphic to Z/6
   Defined on 1 generator
   Relations:
   6*$.1 = 0
   Mapping from: Abelian Group isomorphic to Z/6
   Defined on 1 generator
   Relations:
   6*$.1 = 0 to CrvEll: X14modW2
   Composition of Mapping from: Abelian Group isomorphic to Z/6
   Defined on 1 generator
   Relations:
   6*$.1 = 0 to Set of points of Elliptic Curve defined by y^2 = x^3 - 1664*x^2 - 1404928*x over Rational Field with coordinates in Rational Field given by a rule [no inverse] and
   Elliptic curve isomorphism from: Elliptic Curve defined by y^2 = x^3 - 1664*x^2 - 1404928*x over Rational Field to CrvEll: X14modW2
   Taking (x : y : 1) to (1/256*x : 1/4096*y : 1)
   true true

We now show that we can find two :math:`\QQ(-7)` points on
:math:`X_0(14)` that map to the generator of the :math:`\QQ` points on
this quotient. This proves that all :math:`\QQ` points on the quotient
come from :math:`\QQ(\sqrt{-7})` points and not from :math:`K` points.

::

   sage: _ = magma.eval("L := QuadraticField(-7);")
   sage: _ = magma.eval("X14L := BaseChange(X14, L);")
   sage: _ = magma.eval("phiL := TwoIsogeny(X14L ! P);")
   sage: _ = magma.eval("P1 := Generators(X14L)[1];")
   sage: _ = magma.eval("P2 := Generators(X14L)[2];")
   sage: _ = magma.eval("Q := Generators(X14modW2)[1];")
   sage: print(magma.eval("X14modW2 ! phiL(P1 + P2) eq Q;"))
   true
   sage: print(magma.eval("X14modW2 ! phiL(P1 + 4*P2) eq Q;"))
   true
   sage: print(magma.eval("P1 + P2 eq P1 + 4*P2;"))
   false

We now perform the same procedure for the case :math:`l = 13`, only in
this case the curve :math:`X_0(26)` we start with has genus 2.

::

   sage: _ = magma.eval("X26 := SmallModularCurve(26);")
   sage: _ = magma.eval("w2 := AtkinLehnerInvolution(X26, 26, 2);")
   sage: print(magma.eval("Genus(X26);"))
   2

In this case we can obtain the quotient :math:`X_0(26) / w_2` as the
quotient by the automorphism subgroup generated by :math:`w_2`. This
quotient is an elliptic curve.

::

   sage: _ = magma.eval("G2 := AutomorphismGroup(X26, [w2]);")
   sage: _ = magma.eval("X26modW2, phi := CurveQuotient(G2);")
   sage: print(magma.eval("Genus(X26modW2);"))
   1

We show that the the curve :math:`X_0(26) / w_2` only has three
rational points and explicitly give the 6 points on :math:`X_0(26)`
that lie above them. Four of these points are :math:`\QQ` points and
two are :math:`\QQ(\sqrt{13})`, hence none can be :math:`K` points.

::

   sage: print(magma.eval("AbelianGroup(X26modW2);"))
   Abelian Group isomorphic to Z/3
   Defined on 1 generator
   Relations:
   3*$.1 = 0
   Mapping from: Abelian Group isomorphic to Z/3
   Defined on 1 generator
   Relations:
   3*$.1 = 0 to Set of points of X26modW2 with coordinates in Rational Field given by a rule [no inverse]
   true true
   sage: _ = magma.eval("Q := Generators(X26modW2)[1];")
   sage: print(magma.eval("phi(X26 ! [0, 0, 1]) eq Q;"))
   true
   sage: print(magma.eval("phi(X26 ! [1, 0, 0]) eq Q;"))
   true
   sage: print(magma.eval("phi(X26 ! [0, 1, 1]) eq 2*Q;"))
   true
   sage: print(magma.eval("phi(X26 ! [1, 1, 0]) eq 2*Q;"))
   true
   sage: _ = magma.eval("L<s> := QuadraticField(13);")
   sage: _ = magma.eval("X26L := BaseChange(X26, L);")
   sage: _ = magma.eval("phiL := phi(L);")
   sage: print(magma.eval("X26modW2 ! phiL(X26L ! [1, s, -1]) eq 3*Q;"))
   true
   sage: print(magma.eval("X26modW2 ! phiL(X26L ! [-1, s, 1]) eq 3*Q;"))
   true

Newform elimination
-------------------

Now we perform the computation as mentioned in the last part of
Section 6.5 of the article.

First we load all the newforms corresponding to ``E1c`` and ``E2c``
from the files "tmp/E1.nfs" and "tmp/E2.nfs" respectively. 

::

   sage: nfs1 = E1c.newform_candidates(algorithm='file', path='tmp/E1.nfs')
   sage: nfs2 = E2c.newform_candidates(algorithm='file', path='tmp/E2.nfs')

Now we verify the table of data about these newforms. For each
computed set of newforms we compute in this order: The level of the
newforms, the corresponding character, the dimension of this space of
newforms, the number of galois conjugacy classes of newforms, the
possible sizes of the galois conjugacy classes of newforms, and the
total number of newforms among all conjugacy classes.

::

   sage: eps_m = magma.FullDirichletGroup(15).Elements()[4]
   sage: nfs1[1][0][0].level()
   11520
   sage: eps = nfs1[1][0][0].character(); eps
   Dirichlet character modulo 15 of conductor 15 mapping 11 |--> -1, 7 |--> zeta4
   sage: eps(11) == eps_m(11) and eps(7) == eps_m(7)
   True
   sage: magma.DimensionNewCuspForms(magma.DirichletGroup(nfs1[1][0][0].level(),
   ....: eps_m.CoefficientRing())(eps_m), 2)
   192
   sage: len(nfs1[1][0])
   30
   sage: set(nf.coefficient_field().degree() for nf in nfs1[1][0])
   {4, 8, 16, 24, 32, 48}
   sage: sum(nf.coefficient_field().degree() for nf in nfs1[1][0])
   384
   sage: nfs1[0][0][0].level()
   23040
   sage: eps = nfs1[0][0][0].character(); eps
   Dirichlet character modulo 15 of conductor 15 mapping 11 |--> -1, 7 |--> zeta4
   sage: eps(11) == eps_m(11) and eps(7) == eps_m(7)
   True
   sage: magma.DimensionNewCuspForms(magma.DirichletGroup(nfs1[0][0][0].level(),
   ....: eps_m.CoefficientRing())(eps_m), 2)
   384
   sage: len(nfs1[0][0])
   20
   sage: set(nf.coefficient_field().degree() for nf in nfs1[0][0])
   {8, 40, 48}
   sage: sum(nf.coefficient_field().degree() for nf in nfs1[0][0])
   768
   sage: nfs2[0].level()
   15360
   sage: eps = nfs2[0].character(); eps
   Dirichlet character modulo 15 of conductor 15 mapping 11 |--> -1, 7 |--> zeta4
   sage: eps(11) == eps_m(11) and eps(7) == eps_m(7)
   True
   sage: magma.DimensionNewCuspForms(magma.DirichletGroup(nfs2[0].level(),
   ....: eps_m.CoefficientRing())(eps_m), 2)
   752
   sage: len(nfs2)
   14
   sage: set(nf.coefficient_field().degree() for nf in nfs2)
   {16, 64, 80, 96, 128, 176, 192}
   sage: sum(nf.coefficient_field().degree() for nf in nfs2)
   1504

As we can see the newforms for ``E2c`` have quite large coefficient
fields. The code requires to compute the composite field of these
fields and the image field of the corresponding character which would
take very long using the methods in SAGE. Therefore we help the code
by preloading the fact that the coefficient field already contains the
field of the character.

::

   sage: for i in z:
   ....:     f = nfs2[i]
   ....:     Kf = f.coefficient_field()
   ....:     Lf = f.character().base_ring()
   ....:     mapK = Kf.hom(Kf)
   ....:     mapL = Lf.embeddings(Kf)[0]
   ....:     composite_field.cache[((Kf, Lf, True),())] = (Kf, mapK, mapL)
   ....:     composite_field.cache[((Lf, Kf, True),())] = (Kf, mapL, mapK)
   ....:     composite_field.cache[((Kf, Lf, False),())] = Kf
   ....:     composite_field.cache[((Lf, Kf, False),())] = Kf
   ....: 

Now we perform the elimination process described in the article for
both curves separately.

::
   
   sage: nfs1 = eliminate_by_traces(E1c, nfs1, condition=coprime, primes=prime_range(7, 40))
   sage: nfs2 = eliminate_by_traces(E2c, nfs2, condition=coprime, primes=prime_range(7, 40))

Next we eliminate for each newform :math:`g` the prime factors 2, 3,
and 5 from the number :math:`M_g` described in the article.

::

   sage: nfs1 = eliminate_primes(E1c, nfs1, 2*3*5)
   sage: nfs2 = eliminate_primes(E2c, nfs2, 2*3*5)

We check that the number of newforms now remaining matches the claim
in the article.

::

   sage: nfs1[1][0][0][0].level()
   11520
   sage: len(nfs1[1][0])
   14
   sage: nfs1[0][0][0][0].level()
   23040
   sage: len(nfs1[0][0])
   12
   sage: nfs2[0][0].level()
   15360
   sage: len(nfs2)
   7

Lastly we combine all remaining newforms and perform the multi-Frey
elimination resulting in no newforms remaining.

::

   sage: nfs = combine_newforms(nfs1, nfs2)
   sage: nfs = eliminate_by_traces((E1c, E2c), nfs, condition=coprime, primes=prime_range(7, 50))
   sage: nfs
   []
