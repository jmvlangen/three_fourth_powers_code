r"""A tree implementation for storing sets of p-adic numbers known as a
p-adic tree.

A p-adic tree is a tree that satisfies the following properties:

 - There is a single p-adics used throughout the tree defined by a
   common pAdicBase object stored in each node.

 - Each node is labeled by a tuple of elements of the number field of
   the p-adics. The length of this tuple is the same for each node in
   the tree and is known as the width of the tree. Furthermore the
   elements of this tuple can only be those defined by the method
   :meth:`representatives` of the pAdicBase object defining the
   p-adics.

 - Each node can have nodes that are its children, which will have
   that node as their parent. All children of a node should have
   distinct labels.

 - There exists a unique node that has no parent, called the root of
   the tree.

Furthermore we have the following properties and definitions

 - Each infinite path of the tree starting at the root uniquely
   defines a tuple of p-adic numbers of length equal to the width. If
   the nodes this path passes through, excluding the root, are labeled
   in order by $(a_{1,1}, \ldots, a_{1,n}), (a_{2,1}, \ldots,
   a_{2,n}), ldots$ then the corresponding unique tuple of p-adic
   numbers is ..MATH::

       (a_{1,1} + a_{2,1} \pi + a_{3,1} \pi^2 + \ldots, \ldots,
       a_{1,n} + a_{2,n} \pi + a_{3,n} \pi^2 + \ldots),

   where $\pi$ is the uniformizer of the p-adics associated with this
   tree.

 - We will say that a tuple of p-adic numbers of length the width of
   this tree is in the tree if and only if the corresponding infinite
   branch is in the tree. This makes the tree represent sets of p-adic
   numbers. In this sense all set theoretic operations on p-adics
   trees are defined.

 - The path from the root to a node in the tree defines all tuples of
   p-adic numbers corresponding to infinite paths through that node up
   to a power of the prime of the p-adics. This means we can get a
   tuple of elements of the number field of the p-adics that defines
   this element. We will call this the representative of a node.

 - We will call the length of a path from the root to a node the level
   of that node. Note that the representative of a node of level $n$
   defines all tuples of p-adics numbers corresponding to paths
   through that node up to the prime of the p-adics to the power $n$.

For the implementation of a p-adic tree there are several
classes. First of all there is the class pAdicNode which implements
the basic behavior of a node in a p-adic tree. It makes use of the
class pAdicNodeCollection, which represents a collection of pAdicNodes
that do not all have the same label, to store its children. Using the
class pAdicNodeCollection_inverted which immitates a
pAdicNodeCollection in which all nodes are the root of a tree with all
possible infinite paths but only a few exceptions, one can make trees
out of pAdicNodes that do not represent the empty set.

The second class is pAdicTree, which provides a set like interface to
a p-adic tree defined by pAdicNodes. Furthermore a pAdicTree stores a
list of names, known as variables, of length equal to the with of the
tree. For a tuple of p-adic numbers in this p-adic tree, the i-th
entry will be linked to the i-th variable. Set theoretic operations on
a pAdicTree will keep into account to which value a variable is
linked.

It is important to note that performing operations directly on a
pAdicNode will change the tree it defines. The p-adic tree stored in a
pAdicTree is assumed to be immutable however. Any operations performed
on a pAdicTree will be performed on a copy of the stored p-adic
tree. Even methods that present nodes in the tree will give nodes of a
copy of the original tree. For long computations in which intermediate
steps don't have to be saved it might therefore be useful to work with
the root of the underlying p-adic tree, rather than a pAdicTree
object.

EXAMPLES:

Creation of a tree::

    sage: T = pAdicTree('x', prime=7); T
    p-adic tree for the variables ('x',) with respect to p-adics given by Rational Field and (7)
    sage: T.root()
    p-adic node represented by (0,) with 7 children
    sage: T.pAdics()
    p-adics given by Rational Field and (7)

Operations on trees::

    sage: T1 = pAdicTree(('x', 'y'), prime=2)
    sage: T2 = pAdicTree(('y', 'z'), prime=2)
    sage: T1.union(T2)
    p-adic tree for the variables ('x', 'y', 'z') with respect to p-adics given by Rational Field and (2)
    sage: T1.complement()
    p-adic tree for the variables ('x', 'y') with respect to p-adics given by Rational Field and (2)

Manipulating the tree manually::

    sage: T = pAdicTree(('a', 'b'), prime=2)
    sage: N = T.root()
    sage: N.children.remove_by_coefficients((0,1))
    sage: N.children.remove_by_coefficients((1,1))
    sage: N.children.add(pAdicNode(pAdics=N.pAdics(), coefficients=(0,1)))
    sage: N.children.get((0,1)).children.add(pAdicNode(pAdics=N.pAdics(), width=2, full=True))
    sage: T = pAdicTree(('a', 'b'), root=N)
    sage: ls, I = T.give_as_congruence_condition()
    sage: ls
    [(0, 0), (0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 2), (3, 0), (3, 2)]
    sage: I
    Principal ideal (4) of Integer Ring

AUTHORS:

- Joey van Langen (2019-02-25): initial version

"""
import weakref

# ****************************************************************************
#       Copyright (C) 2019 Joey van Langen <j.m.van.langen@vu.nl>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

class pAdicNode(SageObject):
    r"""A node of a p-adic tree.
    
    A p-adic tree is a tree that satisfies the following properties:

     - There is a single p-adics used throughout the tree defined by a
       common pAdicBase object stored in each node.

     - Each node is labeled by a tuple of elements of the number field of
       the p-adics. The length of this tuple is the same for each node in
       the tree and is known as the width of the tree. Furthermore the
       elements of this tuple can only be those defined by the method
       :meth:`representatives` of the pAdicBase object defining the
       p-adics.

     - Each node can have nodes that are its children, which will have
       that node as their parent. All children of a node should have
       distinct labels.

     - There exists a unique node that has no parent, called the root of
       the tree.

    Furthermore we have the following properties and definitions

     - Each infinite path of the tree starting at the root uniquely
       defines a tuple of p-adic numbers of length equal to the width. If
       the nodes this path passes through, excluding the root, are labeled
       in order by $(a_{1,1}, \ldots, a_{1,n}), (a_{2,1}, \ldots,
       a_{2,n}), ldots$ then the corresponding unique tuple of p-adic
       numbers is ..MATH::

           (a_{1,1} + a_{2,1} \pi + a_{3,1} \pi^2 + \ldots, \ldots,
           a_{1,n} + a_{2,n} \pi + a_{3,n} \pi^2 + \ldots),

       where $\pi$ is the uniformizer of the p-adics associated with this
       tree.

     - We will say that a tuple of p-adic numbers of length the width of
       this tree is in the tree if and only if the corresponding infinite
       branch is in the tree. This makes the tree represent sets of p-adic
       numbers. In this sense all set theoretic operations on p-adics
       trees are defined.

     - The path from the root to a node in the tree defines all tuples of
       p-adic numbers corresponding to infinite paths through that node up
       to a power of the prime of the p-adics. This means we can get a
       tuple of elements of the number field of the p-adics that defines
       this element. We will call this the representative of a node.

     - We will call the length of a path from the root to a node the level
       of that node. Note that the representative of a node of level $n$
       defines all tuples of p-adics numbers corresponding to paths
       through that node up to the prime of the p-adics to the power $n$.
    
    EXAMPLE::

        sage: pAdics = pAdicBase(ZZ, 3)
        sage: R = pAdicNode(pAdics=pAdics)
        sage: R.children
        []
        sage: N = pAdicNode(pAdics=pAdics, coefficients=(2,), full=True)
        sage: R.children.add(N)
        sage: R.children
        [p-adic node represented by (2,) with 3 children]
        sage: N.parent() == R
        True
        sage: N.children.list()
        [p-adic node represented by (2,) with 3 children,
         p-adic node represented by (5,) with 3 children,
         p-adic node represented by (8,) with 3 children]

    """
    
    def __init__(self, parent=None, children=None, pAdics=None,
                 coefficients=None, full=False, width=1):
        r"""Initialize this p-adic node.
        
        INPUT:
        
        - ``parent`` -- A pAdicNode or None (default: None) which is
          either the parent of this node or None if it should be the
          root of a p-adic tree.

        - ``children`` -- A pAdicNodeCollection or None (default:
          None). If it is a pAdicNodeCollection it should be the
          collection of children of this node. If it is None it will
          be initialized as an empty or full collection depending on
          the argument ``full``

        - ``pAdics`` -- A pAdicBase object or None (default:None).
          This is the p-adics that should be used for this node.  It
          should be specified unless `parent` is given, in which case
          it can be None. If the `parent` argument is given the
          p-adics will be set to that of the parent node. Note that
          the p-adics should be the same throughout the tree.

        - ``coefficients`` -- A tuple of numbers or None (default:
          None). This is the label of this node.  Note that for
          working correctly the tuple must consist of representatives
          of the residue field of the p-adics of this node, as given
          by the pAdicBase object that defines the p-adics, however
          there is no check to ensure that this is the case.  If this
          argument is None, the coefficients will be set to a tuple of
          zeroes.

        - ``full`` -- A boolean value (default: False). If set to True
          this node will be assumed to be the root of a p-adic tree
          that contains all possible infinite paths. If set to False
          this node will be assumed to have no children at all. If the
          argument `children` is specified this argument will be
          ignored.

        - ``width`` -- A strictly positive integer (default: 1)
          describing the length of the argument `coefficients`. This
          should be the same throughout the tree. It will be ignored
          if either the `coefficients` or the `parent` argument is
          given. If the `parent` argument is given, it will be set to
          the width of the parent. If the `parent` argument is not
          given, but the `coefficients` argument is, it will be set to
          the length of the tuple given as `coefficients`.

        EXAMPLES::

            sage: pAdics = pAdicBase(ZZ, 5)
            sage: N = pAdicNode(pAdics=pAdics); N
            p-adic node represented by (0,) with 0 children
            sage: pAdicNode(parent=N)
            p-adic node represented by (0,) with 0 children
            sage: pAdicNode(pAdics=pAdics, full=True)
            p-adic node represented by (0,) with 5 children
            sage: pAdicNode(pAdics=pAdics, coefficients=(2, 3))
            p-adic node represented by (2, 3) with 0 children
            sage: pAdicNode(pAdics=pAdics, width=3)
            p-adic node represented by (0, 0, 0) with 0 children

        """
        if parent is None:
            self._parent = None
            if pAdics is None or not isinstance(pAdics, pAdicBase):
                raise ValueError("Should specify pAdics if no parent given.")
            self._pAdics = pAdics
            if coefficients is None:
                self.width = width
                self.coefficients = tuple([self.pAdics().zero()]*self.width)
            elif isinstance(coefficients, tuple):
                self.width = len(coefficients)
                self.coefficients = coefficients
            else:
                raise ValueError("The argument coefficients is not a tuple.")
        elif isinstance(parent, pAdicNode):
            self._parent = weakref.ref(parent)
            self._pAdics = parent.pAdics()
            self.width = parent.width
            if coefficients is None:
                self.coefficients = tuple([self.pAdics().zero()]*self.width)
            elif isinstance(coefficients, tuple):
                if len(coefficients) == self.width:
                    self.coefficients = coefficients
                else:
                    raise ValueError("The coefficients argument has the wrong"+
                                     "length.")
            else:
                raise ValueError("The argument coefficients is not a tuple.")
        else:
            raise ValueError("%s is not a valid parent."%(parent,))
            
        if children is None:
            if full:
                children = pAdicNodeCollection_inverted(self)
            else:
                children = pAdicNodeCollection(self)
        if not isinstance(children, pAdicNodeCollection):
            raise ValueError("%s is not a collection of pAdic nodes"%children)
        self.children = children
        self.children.update_parent(self)
        self._update_sub_tree()
        
    def _similar_node(self, other):
        r"""Check whether this and another node are compatible.
                
        Two nodes are compatible iff they both have the same p-adics
        and width.
        
        Note that this function also checks whether the other object
        given is a p-adic node.
        
        INPUT:
        
        - ``other`` -- Any object.
        
        OUTPUT:

        True if `other` is an instance of pAdicNode with the same
        p-adics and width. False in all other cases.

        """
        return (isinstance(other, pAdicNode) and
                self.pAdics() == other.pAdics() and
                self.width == other.width)
            
    def _set_parent(self, parent):
        r"""Set the parent of this node and update subtree accordingly.

        Changes the parent of this node to the given parent if the
        parent is similar according to :func:`_similar_node`.
        It will also reset all values that depend on the hierarchy of
        the nodes for this node and all nodes below it.
        
        .. NOTE::

        Do not use! For internal purposes only.

        INPUT:
        
        - ``parent`` -- A pAdicNode similar to this one.

        """
        if not self._similar_node(parent):
            raise ValueError("%s is not similar to %s"%(parent, self))
        self._parent = weakref.ref(parent)
        #reset variables that are not correct after changing the parent
        self._update_sub_tree()
        
    def _update_sub_tree(self):
        r"""Reset hierarchy dependent variables of this node and all below it.
        
        To prevent having to repeat recursive computations, each
        pAdicNode object caches information that has to be calculated
        recursively.  Since this information depends on the structure
        above the node, this information has to be recalculated when
        this structure changes. This method makes sure this happens.

        """
        self._rep = None
        self.children._update_existing_children()
    
    def parent(self):
        r"""Give the parent of this node
        
        OUTPUT:

        A pAdicNode object that is the parent of this node or None if
        it has no parent.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 2)
            sage: N = pAdicNode(pAdics=pAdics, full=True)
            sage: N.parent() == None
            True
            sage: N.children.list()[1].parent() == N
            True

        """
        if self._parent is None:
            return None
        return self._parent()
        
    def is_root(self):
        r"""Determine whether this node is a root.
        
        OUTPUT:

        True if this node is the root of the p-adic tree it is part
        of. False otherwise.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 7)
            sage: N = pAdicNode(pAdics=pAdics, full=True)
            sage: N.is_root()
            True
            sage: N.children.list()[0].is_root()
            False

        """
        return self.parent() is None
        
    def root(self):
        r"""Give the root of the p-adic tree this node is in.
        
        OUTPUT:

        The unique node above this one that has no parent.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 5)
            sage: N = pAdicNode(pAdics=pAdics, full=True)
            sage: N.root() == N
            True
            sage: N.children.list()[0].root() == N
            True

        """
        if self.is_root():
            return self
        else:
            return self.parent().root()
        
    def representative(self):
        r"""A representation of this node as a tuple of numbers.
        
        The representation of this node will be a tuple of zeroes
        if it is the root and it will be
        .. MATH:
        
            r + c * \pi^(l-1)
            
        where `r` is the representation of its parent, `c` is the
        coefficients of this node and `\pi` is the uniformizer
        returned by the p-adics of the tree this node belongs to.
        
        .. NOTE::

        This function is cached.
        
        OUTPUT:

        A tuple of elements of the number field of the p-adics of the
        tree this node is part of, such that all infinite paths from
        the root through this node correspond to tuples of p-adic
        numbers that are equivalent to this tuple modulo $P^n$, where
        $P$ is the prime of the p-adics and $n$ is the level of this
        node.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 7)
            sage: N = pAdicNode(pAdics=pAdics, full=True, width=2)
            sage: N.representative()
            (0, 0)
            sage: N.children.list()[11].representative()
            (4, 1)

        .. SEEALSO::

            :meth:`level`

        """
        if self.is_root():
            return self.coefficients
        if not hasattr(self, "_rep") or self._rep is None:
            self._rep = list(self.parent().representative())
            for i in range(self.width):
                self._rep[i] += (self.coefficients[i] *
                                 self.pAdics().uniformizer()^(self.level()-1))
            self._rep = tuple(self._rep)
        return self._rep
        
    def quotient_tuple(self):
        r"""A representation of this node as a tuple of numbers in a
        corresponding quotient ring.
        
        A representation as a tuple of elements of a quotient ring is
        the same representation as returned by :meth:`representative`
        but then considered as an element of $R / (P^n)$, where $R$ is
        the ring of integers of the p-adics of this tree, $P$ is the
        prime ideal of the p-adics of this tree and $n$ is the level of this
        node.
        
        OUTPUT:

        A tuple of elements of $R / (P^n)$ where $R$ is the ring of
        integers of the p-adics of this node, $P$ is the prime ideal
        of the p-adics of this tree and $n$ is the level of this
        node. This is the reduction modulo $P^n$ of each tuple of
        p-adic numbers that corresonds to an infinite path from the
        root through this node.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 5)
            sage: N = pAdicNode(pAdics=pAdics, full=True, width=2)
            sage: N.quotient_tuple()
            (0, 0)
            sage: N.quotient_tuple()[0].parent()
            Ring of integers modulo 1
            sage: N2 = N.children.list()[7].children.list()[13]
            sage: N2.quotient_tuple()
            (17, 11)
            sage: N2.quotient_tuple()[0].parent()
            Ring of integers modulo 25

        .. SEEALSO::

            :meth:`representative`
            :meth:`level`

        """
        S = self.pAdics().quotient_ring(self.level())
        return tuple([S(a) for a in self.representative()])
        
    def pAdics(self):
        r"""Return the p-adics of the p-adic tree.
        
        OUTPUT:

        A pAdicBase object that has the p-adics of the p-adic tree
        this node belongs to.

        EXAMPLE::

            sage: pAdics = pAdicBase(QQ, 3)
            sage: N = pAdicNode(pAdics=pAdics, full=True)
            sage: N.pAdics()
            p-adics given by Rational Field and (3)
            sage: N.children.list()[0].pAdics()
            p-adics given by Rational Field and (3)

        """
        if not hasattr(self, "_pAdics") or self._pAdics is None:
            if self.is_root():
                raise ValueError("Found a p-adic tree without p-adics")
            self._pAdics = self.parent().pAdics()
        return self._pAdics
        
    def level(self):
        r"""Give the level of this node.
        
        OUTPUT:

        The length of the shortest path from the root to this node.

        EXAMPLE::

            sage: pAdics = pAdicBase(QQ, 2)
            sage: R = pAdicNode(pAdics=pAdics, full=True)
            sage: N = R; N.level()
            0
            sage: N = N.children.list()[0]; N.level()
            1
            sage: N = N.children.list()[0]; N.level()
            2
            sage: N = N.children.list()[0]; N.level()
            3

        """
        if self.is_root():
            return 0
        else:
            return self.parent().level() + 1
            
    def parent_at_level(self, n, my_level=None):
        r"""Give the node at level `n` above this node.
        
        INPUT:
        
        - `n` -- A non-negative integer that is the level of the node
          we are looking for. This should at most be the level of this
          node.

        - `my_level` -- A non-negative integer (default:
          self.level()).  This argument should equal the level of this
          node.  It is used internally to prevent the recursion needed
          for self.level(). Do not use unless you know the level of
          this node beforehand.
          
        OUTPUT:

        The pAdicNode at level `n` that is in the parent chain of this
        node.

        EXAMPLE::

            sage: pAdics = pAdicBase(QQ, 2)
            sage: R = pAdicNode(pAdics=pAdics, full=True)
            sage: N = R.children_at_level(4)[13]
            sage: N.parent_at_level(0)
            p-adic node represented by (0,) with 2 children
            sage: N.parent_at_level(0) == R
            True
            sage: N.parent_at_level(1)
            p-adic node represented by (1,) with 2 children
            sage: N.parent_at_level(2)
            p-adic node represented by (3,) with 2 children
            sage: N.parent_at_level(3)
            p-adic node represented by (3,) with 2 children
            sage: N.parent_at_level(4)
            p-adic node represented by (11,) with 2 children
            sage: N.parent_at_level(4) == N
            True
            sage: N.parent_at_level(5)
            Traceback (most recent call last):
            ...
            ValueError: p-adic node represented by (11,) with 2 children does not have a parent at level 5

        .. SEEALSO::

            :meth:`level`
            :meth:`parent`
        
        """
        if my_level is None:
            my_level = self.level()
        if n == my_level:
            return self
        elif n < my_level:
            return self.parent().parent_at_level(n, my_level=my_level-1)
        else:
            raise ValueError(str(self) + " does not have a parent at level " +
                             str(n))
    
    def count_children_at_level(self, n, my_level=None):
        r"""Give the number of nodes at level `n` below this one.
        
        INPUT:
        
        - `n` -- A non-negative integer that is the level of which we
          want to count the number of nodes.

        - `my_level` -- A non-negative integer (default:
          self.level()).  This should always equal the level of this
          node. It is used internally to prevent the recursion needed
          for self.level(). Do not use unless you know the level of
          this node beforehand.
          
        OUTPUT:

        A non-negative integer equal to the number of nodes at level
        `n` that have a path to them from the root through this node.

        EXAMPLE::

            sage: pAdics = pAdicBase(QQ, 5)
            sage: R = pAdicNode(pAdics=pAdics, full=True)
            sage: N = R.children_at_level(2)[13]
            sage: N.count_children_at_level(4)
            25
            sage: N.count_children_at_level(3)
            5
            sage: N.count_children_at_level(2)
            1
            sage: N.count_children_at_level(1)
            0

        .. SEEALSO::

            :meth:`children_at_level`
            :meth:`level`
            :meth:`parent_at_level`

        """
        if my_level is None:
            my_level = self.level()
        if n < my_level:
            return 0
        elif n == my_level:
            return 1
        elif n == my_level + 1:
            return self.children.size()
        elif self.is_full():
            return self.children.size()^(n - my_level)
        else:
            result = 0
            for child in self.children:
                result += child.count_children_at_level(n, my_level=my_level+1)
            return result
    
    def children_at_level(self, n, my_level=None):
        r"""Give a list of nodes at level `n` below this one.
        
        INPUT:
        
        - `n` -- A non-negative integer that is the level of the nodes
          we want to get.

        - `my_level` -- A non-negative integer (default:
          self.level()). This should always equal the level of this
          node. It is used internally to prevent the recursion needed
          for self.level(). Do not use unless you know the level of
          this node beforehand.
          
        OUTPUT:

        A list of all nodes at level `n` that have a path to them from
        the root through this node.

        EXAMPLE::

            sage: pAdics = pAdicBase(QQ, 2)
            sage: R = pAdicNode(pAdics=pAdics, full=True)
            sage: N = R.children_at_level(2)[3]
            sage: N.children_at_level(4)
            [p-adic node represented by (3,) with 2 children,
             p-adic node represented by (11,) with 2 children,
             p-adic node represented by (7,) with 2 children,
             p-adic node represented by (15,) with 2 children]
            sage: N.children_at_level(3)
            [p-adic node represented by (3,) with 2 children,
             p-adic node represented by (7,) with 2 children]
            sage: N.children_at_level(2)
            [p-adic node represented by (3,) with 2 children]
            sage: N.children_at_level(1)
            []

        """
        if my_level is None:
            my_level = self.level()
        if n == my_level + 1:
            return self.children.list()
        if n > my_level:
            result = []
            for child in self.children:
                 result.extend(child.children_at_level(n, my_level=my_level+1))
            return result
        elif n == my_level:
            return [self]
        else:
            return []
            
    def minimum_full_level(self, my_level=None):
        r"""Give the smallest level at which all nodes below this one are full.

        A node is called full if every possible infinite path from the
        root through that node exist.
        
        INPUT:
        
        - `my_level` -- A non-negative integer (default:
        self.level()). This should always equal the level of this
        node. This is used internally to prevent the recursion needed
        for self.level(). Do not use unless you know the level of this
        node for certain.
        
        OUTPUT:

        The smallest integer $n$, such that all nodes at level $n$ and
        below this node are full. Infinity if no such integer exists.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 3)
            sage: R = pAdicNode(pAdics=pAdics, width=2)
            sage: N1 = pAdicNode(pAdics=pAdics, coefficients=(1, 1))
            sage: R.children.add(N1)
            sage: N2 = pAdicNode(pAdics=pAdics, coefficients=(1, 2), full=True)
            sage: R.children.add(N2)
            sage: R.minimum_full_level()
            2
            sage: N1.minimum_full_level()
            2
            sage: N2.minimum_full_level()
            1

        .. SEE_ALSO::

            :meth:`is_full`,
            :meth:`level`,
            :meth:`children_at_level`

        """
        if my_level is None:
            my_level = self.level()
        if self.is_full():
            return my_level
        if self.is_empty():
            return my_level + 1
        return max([child.minimum_full_level(my_level=my_level+1)
                    for child in self.children])
            
    def is_full(self):
        r"""Determine whether this node is full.

        A node is called full if every possible infinite path from the
        root through that node exist.
        
        OUTPUT:

        True if this node and all nodes below it contain all possible
        children. False otherwise.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 3)
            sage: R = pAdicNode(pAdics=pAdics, width=2)
            sage: N1 = pAdicNode(pAdics=pAdics, coefficients=(1, 1))
            sage: N2 = pAdicNode(pAdics=pAdics, coefficients=(1, 2), full=True)
            sage: R.children.add(N1)
            sage: R.children.add(N2)
            sage: R.is_full()
            False
            sage: N1.is_full()
            False
            sage: N2.is_full()
            True

        .. SEEALSO::

            :meth:`is_empty`

        """
        return self.children.is_full()
        
    def is_empty(self):
        r"""Determine whether this node is empty

        A node is called empty if there is no infinite paths from the
        root through this node.
        
        OUTPUT:

        True if all children of this node are empty. False otherwise.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 3)
            sage: R = pAdicNode(pAdics=pAdics, width=2)
            sage: N1 = pAdicNode(pAdics=pAdics, coefficients=(1, 1))
            sage: N2 = pAdicNode(pAdics=pAdics, coefficients=(1, 2), full=True)
            sage: R.children.add(N1)
            sage: R.children.add(N2)
            sage: R.is_empty()
            False
            sage: N1.is_empty()
            True
            sage: N2.is_empty()
            False

        .. SEE_ALSO::

            :meth:`is_full`

        """
        return self.children.is_empty()
        
    def copy(self):
        r"""Give a copy of this node.
        
        .. NOTE::

        The copy does not have a parent, since the copy process copies
        children. Therefore copying the parent would lead to a double
        copy. A copy of the root would result in a deep copy of this
        tree.
        
        OUTPUT:

        A pAdicNode object that is a copy of this one.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 5)
            sage: R = pAdicNode(pAdics=pAdics, full=True)
            sage: R.copy()
            p-adic node represented by (0,) with 5 children
            sage: N = R.children.list()[3]
            sage: N.copy()
            p-adic node represented by (3,) with 5 children
            sage: N.copy().parent() == None
            True

        .. SEEALSO::

             :meth:`pAdicNodeCollection.copy`

        """
        return pAdicNode(pAdics=self.pAdics(),
                         children=self.children.copy(),
                         coefficients=self.coefficients,
                         width=self.width)
                         
    def increase_width(self, n, pAdics=None, coefficients=None):
        r"""Give a new tree with width increased by n.
        
        INPUT:
        
        - ``n`` -- A non negative integer equal to the number of
          additional coefficients in the new width.

        - ``pAdics`` -- A pAdicBase object (default self.pAdics())
          that contains the p-adic information on which the resulting
          p-adic node should be based. This argument should be
          redundant.

        - ``coefficients`` -- A tuple of numbers of length `n`. The
          label of the new node will be the coefficients of this node
          extended with the numbers in this tuple. Note that for
          working correctly the tuple must consist of representatives
          of the residue field of the p-adics of this node, as given
          by the argument `pAdics`, however there is no check to
          ensure that this is the case. If this argument is None, this
          will be initialized as a tuple of zeroes.
          
        OUTPUT:

        A pAdicNode with p-adics as given by the argument `pAdics`,
        coefficients equal to the coefficients of this node extended
        by the given tuple `coefficients`, and as children all
        possible increased width versions of children of this node.

        EXAMPLES::

            sage: pAdics = pAdicBase(QQ, 3)
            sage: N = pAdicNode(pAdics = pAdics, width=2); N
            p-adic node represented by (0, 0) with 0 children
            sage: N.increase_width(1)
            p-adic node represented by (0, 0, 0) with 0 children

        The number of nodes increases accordingly when increasing the
        width::

            sage: pAdics = pAdicBase(QQ, 3)
            sage: N = pAdicNode(pAdics = pAdics, width=2, full=True); N
            p-adic node represented by (0, 0) with 9 children
            sage: N.increase_width(2)
            p-adic node represented by (0, 0, 0, 0) with 81 children

        One can decide what coefficients should fit in the new spots::

            sage: pAdics = pAdicBase(QQ, 3)
            sage: N = pAdicNode(pAdics = pAdics, width=2, full=True); N
            p-adic node represented by (0, 0) with 9 children
            sage: N.increase_width(2, coefficients=(2, 1))
            p-adic node represented by (0, 0, 2, 1) with 81 children

        .. SEEALSO::

            :meth:`decrease_width`
            :meth:`permute_coefficients`

        """
        if pAdics is None:
            pAdics = self.pAdics()
        if coefficients is None:
            coefficients = tuple([pAdics.zero()]*n)
        return pAdicNode(pAdics=pAdics,
                         coefficients=(self.coefficients + coefficients),
                         children=self.children._increase_width(n, pAdics),
                         width=(self.width + n))
                         
    def decrease_width(self, indices, pAdics=None):
        r"""Give a copy of this node with a smaller width.
        
        INPUT:
        
        - ``indices`` -- An iterable object containing distinct
          integers between 0 and the width of this node (0 inclusive,
          width exclusive). These are the indices of the coefficients
          that should be present in the returned node.

        - ``pAdics`` -- A pAdicBase object (default: self.pAdics())
          describing the p-adics of tree that the returned node should
          be part of.
          
        OUTPUT:

        A pAdicNode with the p-adics given by `pAdics` and labeled by
        a tuple of numbers in which the i-th number is the
        indices[i]-th number of the coefficients of this
        node. Furthermore the children of the returned node are those
        obtained from calling :meth:`decrease_width` on the children
        of this node with the same arguments.

        EXAMPLES::

            sage: pAdics = pAdicBase(QQ, 3)
            sage: N = pAdicNode(pAdics = pAdics, width=5); N
            p-adic node represented by (0, 0, 0, 0, 0) with 0 children
            sage: N.decrease_width(range(2))
            p-adic node represented by (0, 0) with 0 children

        The number of children changes accordingly when decreasing the
        width::

            sage: pAdics = pAdicBase(QQ, 3)
            sage: N = pAdicNode(pAdics = pAdics, width=5, full=True); N
            p-adic node represented by (0, 0, 0, 0, 0) with 243 children
            sage: N.decrease_width(range(3))
            p-adic node represented by (0, 0, 0) with 27 children

        We can also choose which indices to keep and in what order::

            sage: pAdics = pAdicBase(QQ, 3)
            sage: N = pAdicNode(pAdics = pAdics, width=5, full=True); N
            p-adic node represented by (0, 0, 0, 0, 0) with 243 children
            sage: N2 = N.children.list()[137]; N2
            p-adic node represented by (2, 0, 0, 2, 1) with 243 children
            sage: N2.decrease_width([1, 4, 0])
            p-adic node represented by (0, 1, 2) with 27 children

        .. SEEALSO::

            :meth:`increase_width`
            :meth:`permute_coefficients`

        """
        if pAdics is None:
            pAdics = self.pAdics()
        coefficients = tuple(self.coefficients[i] for i in indices)
        return pAdicNode(pAdics=pAdics, coefficients=coefficients,
                         children=self.children._decrease_width(indices,
                                                                pAdics),
                         width=len(indices))
                         
    def permute_coefficients(self, permutation, from_root=True):
        """Permute the coefficients of this node.
        
        The permutation will be done in such a way that the i-th entry
        in the new odering will be permutation[i]-th entry of the
        original coefficient.
        
        INPUT:
        
        - ``permutation`` -- a list consisting of the integers 0 to
          the width of this node (0 inclusive, width exclusive), which
          should all appear exactly once. The i-th entry of this list
          should be the index of the coefficient in this node that
          should become the i-th coefficient after permutation.

        - ``from_root`` -- A boolean value (default: True). If set to
          true the coefficients of all nodes in the tree will be
          permuted, whilst the permutation will be limited to this
          node and the ones below it otherwise.

        EXAMPLE::

            sage: pAdics = pAdicBase(QQ, 5)
            sage: R = pAdicNode(pAdics=pAdics, full=True, width=4)
            sage: N = R.children.list()[358]; N
            p-adic node represented by (3, 1, 4, 2) with 625 children
            sage: N.permute_coefficients([1, 3, 0, 2])
            sage: N
            p-adic node represented by (1, 2, 3, 4) with 625 children

        .. SEEALSO::

            :meth:`increase_width`
            :meth:`decrease_width`

        """
        if from_root:
            self.root().permute_coefficients(permutation, from_root=False)
        else:
            self.coefficients = tuple([self.coefficients[permutation[i]]
                                       for i in range(self.width)])
            self._rep = None
            self.children.permute_coefficients(permutation)
    
    def sub_tree(self, children=None):
        r"""Obtain the subtree of this tree containing this node.

        The subtree containing this node is the p-adic tree that
        contains only those nodes in this tree through which there is
        a path from the root that also goes through this node.
        
        INPUT:

        - ``children`` -- A list of nodes that are copies of children
          of this node, or None (default: None). If None the subtree
          will contain all possible children of this node. Otherwise
          the subtree will be limited to only those children given in
          this list.
        
        OUTPUT:

        A pAdicNode that is a copy of the root of the p-adic tree that
        this node is part of. This new tree consists of copies of all
        those nodes in the old tree that have a path through them from
        the root that also passes through this node. If the argument
        `children` was not None, the copy of this node in the new tree
        will have as children precisely the nodes in the list given.

        EXAMPLE::

            sage: pAdics = pAdicBase(QQ, 2)
            sage: R = pAdicNode(pAdics=pAdics, full=True, width=2)
            sage: N = R.children_at_level(2)[7]; N
            p-adic node represented by (3, 2) with 4 children
            sage: R2 = N.sub_tree()
            sage: R2.children_at_level(2)
            [p-adic node represented by (3, 2) with 4 children]

        """
        if children is None:
            node = self.copy()
        else:
            node = pAdicNode(pAdics=self.pAdics(),
                             coefficients=self.coefficients,
                             width=self.width)
            for child in children:
                node.children.add(child)
        if self.is_root():
            return node
        else:
            return self.parent().sub_tree(children=[node])
        
    def remove(self, child=None):
        r"""Remove a node from the p-adic tree.

        This method removes this node from the tree, or if the
        argument `child` is not None, removes that child of this
        node. If by removing a node a node that is not the root has no
        children left that node will also be removed.
        
        .. NOTE::

        The root of a tree can never be removed and attempting to
        remove it will result in a ValueError.
        
        INPUT:
        
        - ``child`` -- A pAdicNode that is a child of this node, or
          the value None (default: None). If not None that child of
          this node wil be removed. If None this node will be removed.

        EXAMPLE::

            sage: pAdics = pAdicBase(QQ, 2)
            sage: R = pAdicNode(pAdics=pAdics, full=True, width=2)
            sage: N = R.children_at_level(2)[7]; N
            p-adic node represented by (3, 2) with 4 children
            sage: N.remove()
            sage: R.children_at_level(2)
            [p-adic node represented by (0, 0) with 4 children,
             p-adic node represented by (2, 0) with 4 children,
             p-adic node represented by (0, 2) with 4 children,
             p-adic node represented by (2, 2) with 4 children,
             p-adic node represented by (1, 0) with 4 children,
             p-adic node represented by (3, 0) with 4 children,
             p-adic node represented by (1, 2) with 4 children,
             p-adic node represented by (0, 1) with 4 children,
             p-adic node represented by (2, 1) with 4 children,
             p-adic node represented by (0, 3) with 4 children,
             p-adic node represented by (2, 3) with 4 children,
             p-adic node represented by (1, 1) with 4 children,
             p-adic node represented by (3, 1) with 4 children,
             p-adic node represented by (1, 3) with 4 children,
             p-adic node represented by (3, 3) with 4 children]

        """
        if child is None:
            if self.is_root():
                raise ValueError("Can not remove the root of a tree.")
            else:
                self.parent().remove(child=self)
        else:
            self.children.remove(child)
            if self.is_empty() and not self.is_root():
                self.remove()
    
    def _from_root_list(self):
        r"""Give a path from the root to this node as a list.

        This list consists of all nodes along the path, including the
        root and this node.

        """
        if self.is_root():
            return [self]
        else:
            result = self.parent()._from_root_list()
            result.append(self)
            return result

    def _merge_with_list(self, ls, index=None):
        r"""Merge a list of nodes into this node.

        Part of the implementation of merging. Use the method
        :meth:`merge` to merge nodes.

        INPUT:

        - ``ls`` -- A list of pAdicNodes with the same p-adics and
          width as this node. The list should start with the root of a
          p-adic tree. Each node in this list should be the parent of
          the next node in the list if there is one.

        - ``index`` -- A non-negative integer equal to the level of
          this node plus one. Will be set to that value by
          default. Used to prevent unnecessary recursion in
          meth:`level`

        """
        if index is None:
            index = self.level()+1
        if index >= len(ls):
            self._merge(ls[-1])
        else:
            a_child = None
            if self.children.contains(ls[index].coefficients):
                a_child = self.children.get(ls[index].coefficients)
            else:
                if index >= len(ls)-1:
                    a_child = ls[index].copy()
                    self.children.add(a_child)
                    return None # The child does not have to merge anymore!
                else:
                    a_child = pAdicNode(pAdics=ls[index].pAdics(),
                                        coefficients=ls[index].coefficients,
                                        width=self.width)
                self.children.add(a_child)
            a_child._merge_with_list(ls, index=index+1)
    
    def _merge(self, other):
        r"""Merge another node into this node.
        
        Part of the implementation of merging. Use the method
        :meth:`merge` to merge nodes.

        INPUT:

        - ``other`` -- A pAdicNode with the same p-adics and width as
          this node.

        """
        if self.is_full():
            return None # Nothing to add
        for child in other.children:
            if self.children.contains(child.coefficients):
                self.children.get(child.coefficients)._merge(child)
            else:
                self.children.add(child.copy())
        
    def merge(self, other, from_root=True):
        r"""Merge another node into this node.
        
        To merge another node into this node means to add copies of
        all children of that node into this node. If a child with the
        same coefficients already exists in this node the new copied
        child will be merged into that child.

        If the option `from_root` was set to True, will make sure that
        the path from the root to the other node in the other p-adic
        tree exists in this p-adic tree and merge the other node with
        the corresponding node in this tree, rather then this
        node.
        
        INPUT:

        - ``other`` -- A pAdicNode with the same p-adics and width as
          this node.

        - ``from_root`` -- A boolean value (default: True). This
          determines whether the two nodes should be merged relative
          to the root or directly.

        EXAMPLE::

            sage: pAdics = pAdicBase(QQ, 3)
            sage: R1 = pAdicNode(pAdics=pAdics, width=2, full=False)
            sage: R2 = pAdicNode(pAdics=pAdics, width=2, full=True)
            sage: N = R2.children_at_level(2)[51]; N
            p-adic node represented by (2, 7) with 9 children
            sage: R1.merge(N)
            sage: R1.children_at_level(2)
            [p-adic node represented by (2, 7) with 9 children]

        .. SEEALSO::

            :meth:`cut`,
            :meth:`limit_to`,
            :meth:`complement`

        """
        if not self._similar_node(other):
            raise ValueError("%s is not similar to %s"%(other, self))
        if from_root:
            self.root()._merge_with_list(other._from_root_list())
        else:
            self._merge(other)
    
    def _cut_list(self, ls, index=None):
        r"""Cut a list of nodes out of this p-adic tree.
        
        Part of the implementation of cutting. Use the method
        :meth:`cut` to cut out nodes.

        INPUT:

        - ``ls`` -- A list of pAdicNodes with the same p-adics and
          width as this node. The list should start with the root of a
          p-adic tree. Each node in this list should be the parent of
          the next node in the list if there is one.

        - ``index`` -- A non-negative integer equal to the level of
          this node plus one. Will be set to that value by
          default. Used to prevent unnecessary recursion in
          meth:`level`

        """
        if index is None:
            index = self.level()+1
        if index >= len(ls):
            self._cut(ls[-1])
        elif self.children.contains(ls[index].coefficients):
            child = self.children.get(ls[index].coefficients)
            child._cut_list(ls, index=index+1)
        # In the remaining case there is nothing to do
    
    def _cut(self, other):
        r"""Cut a node out of this p-adic tree.
        
        Part of the implementation of cutting. Use the method
        :meth:`cut` to cut out nodes.

        INPUT:

        - ``other`` -- A pAdicNode with the same p-adics and width as
          this node.

        """
        if (not self.is_root()) and other.is_full():
            self.remove()
        else:
            for child in other.children:
                if self.children.contains(child.coefficients):
                    self.children.get(child.coefficients)._cut(child)
            
    def cut(self, other, from_root=True):
        r"""Cut out a node from this node.
        
        To cut out a node from this node means to remove all infinite
        paths from this node through its children which correspond to
        infinite paths from the other node through its children. In
        practice this means removing all children from this node for
        which their counterparts in the other node are full and
        cutting out those children of the other node that are not full
        from the corresponding children in this node recursively.

        If the argument `from_root` was set to True, will try to find
        the counterpart of the other node in this p-adic tree and cut
        out the other node from that node. By counterpart we mean the
        node in this tree whose representative is the same as the
        representative of the other node. If such a node does not
        exist, this method does nothing.

        INPUT:

        - ``other`` -- A pAdicNode with the same p-adics and width as
          this node.

        - ``from_root`` -- A boolean value (default: True). This
          determines whether the other node should be cut out relative
          to the root or directly from this node.

        EXAMPLE::

            sage: pAdics = pAdicBase(QQ, 2)
            sage: R = pAdicNode(pAdics=pAdics, width=2, full=True)
            sage: N = R.children_at_level(2)[7]; N
            p-adic node represented by (3, 2) with 4 children
            sage: R.cut(N)
            sage: R.children_at_level(2)
            [p-adic node represented by (0, 0) with 4 children,
             p-adic node represented by (2, 0) with 4 children,
             p-adic node represented by (0, 2) with 4 children,
             p-adic node represented by (2, 2) with 4 children,
             p-adic node represented by (1, 0) with 4 children,
             p-adic node represented by (3, 0) with 4 children,
             p-adic node represented by (1, 2) with 4 children,
             p-adic node represented by (0, 1) with 4 children,
             p-adic node represented by (2, 1) with 4 children,
             p-adic node represented by (0, 3) with 4 children,
             p-adic node represented by (2, 3) with 4 children,
             p-adic node represented by (1, 1) with 4 children,
             p-adic node represented by (3, 1) with 4 children,
             p-adic node represented by (1, 3) with 4 children,
             p-adic node represented by (3, 3) with 4 children]

        .. SEEALSO::

            :meth:`merge`,
            :meth:`limit_to`,
            :meth:`complement`

        """
        if not self._similar_node(other):
            raise ValueError("%s is not similar to %s"%(other, self))
        if from_root:
            self.root()._cut_list(other._from_root_list())
        else:
            self._cut(other)
    
    def _limit_to_list(self, ls, index=None):     
        r"""Limit this p-adic tree to a list of nodes.
        
        Part of the implementation of limiting. Use the method
        :meth:`limit_to` to limit nodes.

        INPUT:

        - ``ls`` -- A list of pAdicNodes with the same p-adics and
          width as this node. The list should start with the root of a
          p-adic tree. Each node in this list should be the parent of
          the next node in the list if there is one.

        - ``index`` -- A non-negative integer equal to the level of
          this node plus one. Will be set to that value by
          default. Used to prevent unnecessary recursion in
          meth:`level`

        """
        if index is None:
            index = self.level() + 1
        if index >= len(ls):
            self._limit_to(self, ls[-1])
        else:
            child = None
            if self.children.contains(ls[index].coefficients):
                child = self.children.get(ls[index].coefficients)
            self.children = pAdicNodeCollection(self)
            if not child is None:
                self.children.add(child)
            
    def _limit_to(self, other):    
        r"""Limit this p-adic tree to a node.
        
        Part of the implementation of limiting. Use the method
        :meth:`limit_to` to limit nodes.

        INPUT:

        - ``other`` -- A pAdicNode with the same p-adics and width as
          this node.

        """
        if self.is_full():
            self.children = other.children.copy()
            self.children.update_parent(self)
            return
        removal_list = []
        for child in self.children:
            if other.children.contains(child.coefficients):
                child._limit_to(other.children.get(child.coefficients))
                if child.is_empty():
                    removal_list.append(child)
            else:
                removal_list.append(child)
        for child in removal_list:
            self.children.remove(child)
    
    def limit_to(self, other, from_root=False):    
        r"""Limit this node to another node.
        
        Limiting this node to another node means that we remove all
        children of this node that are not also children of the other
        node and limit the other children of this node to their
        counterparts in the other node.

        If the argument `from_root` was set to True, will try to find
        the counterpart of the other node in this p-adic tree and
        limit that node to the other node. By counterpart we mean the
        node in this tree whose representative is the same as the
        representative of the other node. If such a node does not
        exist, this method does nothing.
        
        INPUT:

        - ``other`` -- A pAdicNode with the same p-adics and width as
          this node.

        - ``from_root`` -- A boolean value (default: True). This
          determines whether the other node should be cut out relative
          to the root or directly from this node.

        EXAMPLE::

            sage: pAdics = pAdicBase(QQ, 2)
            sage: R1 = pAdicNode(pAdics=pAdics, width=2, full=False)
            sage: R2 = pAdicNode(pAdics=pAdics, width=2, full=True)
            sage: N = R2.children_at_level(2)[7]; N
            p-adic node represented by (3, 2) with 4 children
            sage: R1.merge(N)
            sage: R2.limit_to(R1)
            sage: R2.children_at_level(2)
            [p-adic node represented by (3, 2) with 4 children]

        .. SEEALSO::

            :meth:`merge`,
            :meth:`cut`,
            :meth:`complement`

        """
        if not self._similar_node(other):
            raise ValueError("%s is not similar to %s"%(other, self))
        if from_root:
            self.root()._limit_to_list(other._from_root_list())
        else:
            self._limit_to(other)
            
    def complement(self):
        r"""Give the complement of this node.
        
        The complement of a node is a full node with this node cut
        out.

        OUTPUT:

        A pAdicNode that is the complement of this node.

        EXAMPLE::

            sage: pAdics = pAdicBase(QQ, 2)
            sage: R1 = pAdicNode(pAdics=pAdics, width=2, full=True)
            sage: R1.children_at_level(1)[3].remove()
            sage: R1.children_at_level(2)[0].remove()
            sage: R1.children_at_level(2)[4].remove()
            sage: R1.children_at_level(2)[7].remove()
            sage: R1.children_at_level(2)
            [p-adic node represented by (2, 0) with 4 children,
             p-adic node represented by (0, 2) with 4 children,
             p-adic node represented by (2, 2) with 4 children,
             p-adic node represented by (1, 0) with 4 children,
             p-adic node represented by (1, 2) with 4 children,
             p-adic node represented by (3, 2) with 4 children,
             p-adic node represented by (0, 1) with 4 children,
             p-adic node represented by (0, 3) with 4 children,
             p-adic node represented by (2, 3) with 4 children]
            sage: R2 = R1.complement()
            sage: R2.children_at_level(2)
            [p-adic node represented by (0, 0) with 4 children,
             p-adic node represented by (3, 0) with 4 children,
             p-adic node represented by (2, 1) with 4 children,
             p-adic node represented by (1, 1) with 4 children,
             p-adic node represented by (3, 1) with 4 children,
             p-adic node represented by (1, 3) with 4 children,
             p-adic node represented by (3, 3) with 4 children]

        .. SEEALSO::

            :meth:`merge`,
            :meth:`cut`,
            :meth:`limit_to`
            :meth:`pAdicNodeCollection.complement`

        """
        return pAdicNode(pAdics=self.pAdics(), coefficients=self.coefficients,
                         children=self.children.complement(),
                         width=self.width)
        
    def _repr_(self):
        return ("p-adic node represented by " + str(self.representative()) +
                " with " + str(self.children.size()) + " children")
        
    def __eq__(self, other):
        return (self._similar_node(other) and
                self.children == other.children)
               
    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash((self.coefficients, self.children))
        
class pAdicNodeCollection(SageObject):
    r"""A collection of p-adic nodes indexed by their coefficients.
    
    A pAdicNodeCollection is a collection of p-adic nodes with the
    same p-adics and width such that no two nodes have the same
    coefficients. Furthermore this collection can be the set of
    children of a node, in which case it also stores the common parent
    of these children. Since the collection might be empty, a
    pAdicNodeCollection stores the common p-adics and width of the
    nodes in the collection as well.

    EXAMPLES::

        sage: pAdics = pAdicBase(ZZ, 3)
        sage: C = pAdicNodeCollection(None, pAdics=pAdics, width=2)
        sage: C.add(pAdicNode(pAdics=pAdics, coefficients=(1, 2)))
        sage: C.add(pAdicNode(pAdics=pAdics, coefficients=(2, 2), full=True))
        sage: C.add(pAdicNode(pAdics=pAdics, coefficients=(0, 1), full=True))
        sage: C.add(pAdicNode(pAdics=pAdics, coefficients=(0, 0)))
        sage: C.list()
        [p-adic node represented by (1, 2) with 0 children,
         p-adic node represented by (0, 1) with 9 children,
         p-adic node represented by (0, 0) with 0 children,
         p-adic node represented by (2, 2) with 9 children]
        sage: C.contains((1, 2))
        True
        sage: C.contains((1, 0))
        False
        sage: C.remove_by_coefficients((0, 0))
        sage: C.list()
        [p-adic node represented by (1, 2) with 0 children,
         p-adic node represented by (0, 1) with 9 children,
         p-adic node represented by (2, 2) with 9 children]
        sage: C.size()
        3
        sage: C.maximal_size()
        9
        sage: C.get((2, 2))
        p-adic node represented by (2, 2) with 9 children
        sage: C.complement().list()
        [p-adic node represented by (0, 0) with 9 children,
         p-adic node represented by (1, 0) with 9 children,
         p-adic node represented by (2, 0) with 9 children,
         p-adic node represented by (1, 1) with 9 children,
         p-adic node represented by (2, 1) with 9 children,
         p-adic node represented by (0, 2) with 9 children,
         p-adic node represented by (1, 2) with 9 children]

    The children of a pAdicNode form a p-adic collection and can be
    used as such::

        sage: pAdics = pAdicBase(ZZ, 2)
        sage: N = pAdicNode(pAdics=pAdics, width=2, full=True)
        sage: isinstance(N.children, pAdicNodeCollection)
        True
        sage: N.children.parent() == N
        True
        sage: N.children.get((1, 0))
        p-adic node represented by (1, 0) with 4 children
        sage: N.children.remove_by_coefficients((0, 1))
        sage: N.children.list()
        [p-adic node represented by (0, 0) with 4 children,
         p-adic node represented by (1, 0) with 4 children,
         p-adic node represented by (1, 1) with 4 children]

    """
    
    def __init__(self, parent, pAdics=None, width=1):
        r"""Initialize a pAdicNodeCollection.

        When initialized a pAdicNodeCollection contains no nodes.
        
        INPUT:
        
        - ``parent`` -- A pAdicNode that is the common parent of the
          nodes in this collection, or None if no such node exists.

        - ``pAdics`` -- A pAdicBase object or None (default: None),
          giving the shared p-adics of the nodes in this
          collection. If the argument `parent` is not None it will be
          initialized as the p-adics of this parent. Otherwise it is
          not allowed to be None.

        - ``width`` -- A strictly positive integer that is the common
          width among the nodes in this collection. If the argument
          `parent` is not None it will be initialized as the width of
          this parent.

        EXAMPLES::

            sage: pAdics = pAdicBase(QQ, 5)
            sage: pAdicNodeCollection(None, pAdics=pAdics)
            []

        By giving a parent, no other arguments are required::

            sage: pAdics = pAdicBase(ZZ, 7)
            sage: N = pAdicNode(pAdics=pAdics)
            sage: pAdicNodeCollection(N)
            []
            sage: pAdicNodeCollection(None)
            Traceback (most recent call last):
            ...
            ValueError: Should specify pAdics.

        """
        if parent is None and pAdics is None:
            raise ValueError("Should specify pAdics.")
        if isinstance(parent, pAdicNode):
            self._parent = weakref.ref(parent)
            self._pAdics = parent.pAdics()
            self.width = parent.width
        elif parent is None:
            self._parent = None
            if isinstance(pAdics, pAdicBase):
                self._pAdics = pAdics
            else:
                raise ValueError("%s is not a pAdicBase."%(pAdics,))
            if width in ZZ and width >= 0:
                self.width = width
            else:
                raise ValueError("%s is not a valid width."%(width,))
        else:
            raise ValueError("%s is not a pAdicNode"%parent)
        self._dict = {}
        
    def update_parent(self, parent):
        r"""Change the parent of this collection and the nodes therein.
        
        The parent of this collection and of each node in this
        collection will be set to the argument `parent`.
        
        INPUT:
        
        - ``parent`` -- A pAdicNode that contains this collection as
          its collection of children.

        """
        self._check_pAdic_node(parent)
        self._parent = weakref.ref(parent)
        for v in self._dict.itervalues():
            v._set_parent(parent)
            
    def _update_existing_children(self):
        r"""Reset hierarchy dependent variables of all nodes in this collection.
        
        To prevent having to repeat recursive computations, each
        pAdicNode object caches information that has to be calculated
        recursively. Since this information depends on the structure
        above the node, this information has to be recalculated when
        this structure changes. This method makes sure this happens.

        """
        for v in self._dict.itervalues():
            v._update_sub_tree()
    
    def _check_pAdic_node(self, node):
        r"""Check whether a given object is a suitable p-adic node.

        """
        if not isinstance(node, pAdicNode):
            raise ValueError("%s is not a pAdicNode"%(node,))
        if node.pAdics() != self.pAdics():
            raise ValueError(str(node) + " does not have p-adics like " +
                             str(self.pAdics()))
        if node.width != self.width:
            raise ValueError("%s does not have width %s"%(node, self.width))
            
    def pAdics(self):
        r"""Give the shared p-adics of the nodes in this collection.
        
        OUTPUT:

        A pAdicBase object that gives the p-adics for all nodes in this
        collection.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 5)
            sage: N = pAdicNode(pAdics=pAdics, full=True)
            sage: isinstance(N.children, pAdicNodeCollection)
            True
            sage: N.children.pAdics() == N.pAdics()
            True

        """
        return self._pAdics

    def parent(self):
        r"""Give the common parent of nodes in this collection.
        
        OUTPUT:

        A pAdicNode object that is the parent of all nodes in this
        collection or None if they have no (common) parent.

        EXAMPLES::

            sage: pAdics = pAdicBase(ZZ, 2)
            sage: N = pAdicNode(pAdics=pAdics, full=True)
            sage: isinstance(N.children, pAdicNodeCollection)
            True
            sage: N.children.parent() == N
            True

        There might not be a parent::

            sage: pAdics = pAdicBase(ZZ, 11)
            sage: S = pAdicNodeCollection(None, pAdics=pAdics)
            sage: S.parent() == None
            True

        """
        if self._parent is None:
            return None
        return self._parent()
               
    def add(self, node):
        r"""Add a p-adic node to this collection.
        
        If there already exists a node in this collection with
        the same coefficients as the given node, this function
        will raise an error.
        
        INPUT:
        
        - ``node`` -- A pAdicNode with the same p-adics and width
          as shared among nodes of this collection.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 3)
            sage: R = pAdicNode(pAdics=pAdics, width=2)
            sage: N1 = pAdicNode(pAdics=pAdics, coefficients=(1, 2))
            sage: N2 = pAdicNode(pAdics=pAdics, coefficients=(2, 1))
            sage: N3 = pAdicNode(pAdics=pAdics, coefficients=(2, 1))
            sage: isinstance(R.children, pAdicNodeCollection)
            True
            sage: R.children.add(N1)
            sage: R.children.add(N2)
            sage: R.children.add(N3)
            Traceback (most recent call last):
            ...
            ValueError: A node like p-adic node represented by (2, 1) with 0 children already exists: p-adic node represented by (2, 1) with 0 children
            sage: R.children
            [p-adic node represented by (1, 2) with 0 children,
            p-adic node represented by (2, 1) with 0 children]

        .. SEEALSO::

            :meth:`remove`
            :meth:`remove_by_coefficients`

        """
        self._check_pAdic_node(node)
        if self._dict.has_key(node.coefficients):
            raise ValueError("A node like " + str(node) + " already exists: " +
                             str(self._dict[node.coefficients]))
        self._dict[node.coefficients] = node
        if not self.parent() is None:
            node._set_parent(self.parent())
        
    def contains(self, coefficients):
        r"""Check whether this collection contains a node with given
        coefficients.
        
        INPUT:
        
        - ``coefficients`` -- A tuple of numbers that could be the
          label of a p-adic node in this collection, i.e. the length
          of the tuple should equal the common width of the nodes, the
          numbers must be in the number field of the common p-adics of
          the nodes, and they must be representatives of the residue
          field of this common p-adics as returned by the pAdicBase
          object that gives the p-adics.
        
        OUTPUT:

        True, if there exists a node in this collection with
        coefficients equal to the argument `coefficients`. False,
        otherwise.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 5)
            sage: R = pAdicNode(pAdics=pAdics, width=2, full=True)
            sage: R.children.list()[7].remove()
            sage: isinstance(R.children, pAdicNodeCollection)
            True
            sage: R.children.contains((0,0))
            True
            sage: R.children.contains((2,1))
            False

        .. SEEALSO::

            :meth:`pAdicBase.representatives`

        """
        return self._dict.has_key(coefficients)
        
    def get(self, coefficients):
        r"""Get a node from this collection by its coefficients.
        
        INPUT:
        
        - ``coefficients`` -- A tuple of numbers that could be the
          label of a p-adic node in this collection, i.e. the length
          of the tuple should equal the common width of the nodes, the
          numbers must be in the number field of the common p-adics of
          the nodes, and they must be representatives of the residue
          field of this common p-adics as returned by the pAdicBase
          object that gives the p-adics.
        
        OUTPUT:

        A pAdicNode object in this collection with coefficients equal
        to the argument `coefficients`. The function will raise an
        error if no such node exists.

        EXAMPLE::

            sage: pAdics = pAdicBase(QQ, 3)
            sage: R = pAdicNode(pAdics=pAdics, width=2, full=True)
            sage: isinstance(R.children, pAdicNodeCollection)
            True
            sage: N = R.children.get((1,2)); N
            p-adic node represented by (1, 2) with 9 children
            sage: N.remove()
            sage: R.children.get((1,2))
            Traceback (most recent call last):
            ...
            ValueError: No node with coefficients (1, 2) exists.

        .. SEEALSO::

            :meth:`pAdicBase.representatives`,
            :meth:`contains`

        """
        if not self._dict.has_key(coefficients):
            raise ValueError("No node with coefficients " + str(coefficients) +
                             " exists")
        return self._dict[coefficients]
        
    def list(self):
        r"""Give the nodes in this collection as a list.
        
        OUTPUT:

        A list of the nodes in this collection.

        EXAMPLE::

            sage: pAdics = pAdicBase(QQ, 2)
            sage: R = pAdicNode(pAdics=pAdics, width=2, full=True)
            sage: isinstance(R.children, pAdicNodeCollection)
            True
            sage: R.children.list()
            [p-adic node represented by (0, 0) with 4 children,
             p-adic node represented by (1, 0) with 4 children,
             p-adic node represented by (0, 1) with 4 children,
             p-adic node represented by (1, 1) with 4 children]

        """
        return self._dict.values()
        
    def __iter__(self):
        return self._dict.itervalues()
        
    def size(self):
        r"""Give the number of nodes in this collection.
        
        OUTPUT:

        A non-negative integer equal to the number of nodes in this
        collection.

        EXAMPLE::

            sage: pAdics = pAdicBase(QQ, 3)
            sage: R = pAdicNode(pAdics=pAdics, width=2, full=True)
            sage: isinstance(R.children, pAdicNodeCollection)
            True
            sage: R.children.size()
            9

        .. SEEALSO::

            :meth:`maximal_size`

        """
        return len(self._dict)
        
    def maximal_size(self):
        r"""Give the maximal amount of nodes in this collection.

        Since each node in this collection must have a unique label
        and each label is a tuple of representatives of the residue
        fields of the common p-adics of the nodes, chosen from a fixed
        set of representatives, the number of nodes in this collection
        is limited.
        
        OUTPUT:

        A non-negative integer equal to the number of possible tuples
        that can be coefficients for nodes in this collection.

        EXAMPLE::

            sage: pAdics = pAdicBase(QQ, 7)
            sage: C = pAdicNodeCollection(None, pAdics=pAdics, width=2)
            sage: C.maximal_size()
            49
            sage: C.size()
            0

        .. SEE_ALSO::

            :meth:`size`
            :meth:`pAdicBase.representatives`

        """
        return self.pAdics().size_residue_field()^self.width
        
    def is_full(self):
        r"""Determine whether this collection is full.

        A collection of p-adic nodes is full if it contains the
        maximal amount of nodes and each node in the collection is
        full.
        
        OUTPUT:

        True, if this collections contains the maximal amount
        of nodes and each node is full. False, otherwise.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 3)
            sage: R = pAdicNode(pAdics=pAdics, full=True)
            sage: isinstance(R.children, pAdicNodeCollection)
            True
            sage: C1 = R.children
            sage: C2 = pAdicNodeCollection(None, pAdics=pAdics)
            sage: C3 = C2.copy()
            sage: C3.add(pAdicNode(pAdics=pAdics))
            sage: C1.is_full()
            True
            sage: C2.is_full()
            False
            sage: C3.is_full()
            False

        .. SEEALSO::

            :meth:`is_empty`,
            :meth:`pAdicNode.is_full`,
            :meth:`maximal_size`

        """
        if self.size() != self.maximal_size():
            return False
        for node in self:
            if not node.is_full():
                return False
        return True
        
    def is_empty(self):
        r"""Determine whether this collection is empty.

        A collection of p-adic nodes is called empty if all the nodes
        in the collection are empty.
        
        OUTPUT:

        True, if each node in this collection is empty. False,
        otherwise.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 3)
            sage: R = pAdicNode(pAdics=pAdics, full=True)
            sage: isinstance(R.children, pAdicNodeCollection)
            True
            sage: C1 = R.children
            sage: C2 = pAdicNodeCollection(None, pAdics=pAdics)
            sage: C3 = C2.copy()
            sage: C3.add(pAdicNode(pAdics=pAdics))
            sage: C1.is_empty()
            False
            sage: C2.is_empty()
            True
            sage: C3.is_empty()
            True

        .. SEEALSO::

            :meth:`is_full`,
            :meth:`pAdicNode.is_empty`

        """
        if self.size() == 0:
            return True
        for node in self:
            if not node.is_empty():
                return False
        return True
        
    def remove(self, node):
        r"""Remove a node from this collection
        
        A node is only removed if it was in the collection in the
        first place.
        
        INPUT:
        
        - ``node`` -- A pAdicNode object with the same p-adics and
          with as the common p-adics and width of nodes in this
          collection. If it is in the collection it will be removed
          from the collection.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 2)
            sage: R = pAdicNode(pAdics=pAdics, width=2, full=True)
            sage: isinstance(R.children, pAdicNodeCollection)
            True
            sage: N = R.children.get((1,0))
            sage: R.children.remove(N)
            sage: R.children.list()
            [p-adic node represented by (0, 0) with 4 children,
             p-adic node represented by (0, 1) with 4 children,
             p-adic node represented by (1, 1) with 4 children]

        .. SEEALSO::

            :meth:`add`,
            :meth:`remove_by_coefficients`

        """
        self._check_pAdic_node(node)
        try:
            if self._dict[node.coefficients] == node:
                self._dict.pop(node.coefficients)
        except KeyError:
            pass
            
    def remove_by_coefficients(self, coefficients):
        r"""Remove the node with given coefficients from this collection.
        
        A node is only removed if a node with the given coefficients
        was in this collection in the first place.
        
        INPUT:
        
        - ``coefficients`` -- A tuple of numbers that could be the
          label of a p-adic node in this collection, i.e. the length
          of the tuple should equal the common width of the nodes, the
          numbers must be in the number field of the common p-adics of
          the nodes, and they must be representatives of the residue
          field of this common p-adics as returned by the pAdicBase
          object that gives the p-adics. The p-adic node with the
          given coefficients will be removed from this collection.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 2)
            sage: R = pAdicNode(pAdics=pAdics, width=2, full=True)
            sage: isinstance(R.children, pAdicNodeCollection)
            True
            sage: R.children.remove_by_coefficients((1, 0))
            sage: R.children.list()
            [p-adic node represented by (0, 0) with 4 children,
             p-adic node represented by (0, 1) with 4 children,
             p-adic node represented by (1, 1) with 4 children]

        .. SEEALSO::

            :meth:`add`,
            :meth:`remove`,
            :meth:`pAdicBase.representatives`

        """
        if coefficients in self._dict:
            self._dict.pop(coefficients)

    def copy(self):
        r"""Give a copy of this collection.
        
        .. NOTE::

        The copy does not have a parent, since copies of nodes do not.
        
        OUTPUT:

        A pAdicNodeCollection object that contains copies of the nodes
        in this collection.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 3)
            sage: R = pAdicNode(pAdics=pAdics, width=2, full=True)
            sage: isinstance(R.children, pAdicNodeCollection)
            True
            sage: C = R.children.copy()
            sage: C.list()
            [p-adic node represented by (0, 0) with 9 children,
             p-adic node represented by (1, 0) with 9 children,
             p-adic node represented by (2, 0) with 9 children,
             p-adic node represented by (0, 1) with 9 children,
             p-adic node represented by (1, 1) with 9 children,
             p-adic node represented by (2, 1) with 9 children,
             p-adic node represented by (0, 2) with 9 children,
             p-adic node represented by (1, 2) with 9 children,
             p-adic node represented by (2, 2) with 9 children]

        .. SEEALSO::

             :meth:`pAdicNode.copy`

        """
        result = pAdicNodeCollection(None, pAdics=self.pAdics(),
                                     width=self.width)
        for n in self:
            result.add(n.copy())
        return result
        
    def complement(self):
        r"""Give the complement of this collection.

        The complement of a collection of p-adic nodes is a collection
        of p-adic nodes with the same p-adics and width as the nodes
        in this collection. Furthermore for each tuple $c$ of
        coefficients for such a node we have

        - If $c$ was the coefficients of a full node in the original,
          it does not appear as the coefficients of a node in the
          complement.

        - If $c$ did not appear as the coefficients of a node in the
          original or as the coefficients of an empty node, then $c$
          is the coefficients of a full node in the complement.

        - In any other case the node with coefficients $c$ exists in
          the complement and is the complement of the node with the
          same coefficients in the original.
        
        OUTPUT:

        A pAdicNodeCollection that is the complement of this
        collection.

        EXAMPLE::

            sage: pAdics = pAdicBase(QQ, 3)
            sage: C = pAdicNodeCollection(None, pAdics=pAdics, width=2)
            sage: C.add(pAdicNode(pAdics=pAdics, coefficients=(1,2), full=True))
            sage: N = pAdicNode(pAdics=pAdics, coefficients=(2,1), full=True)
            sage: N.children.remove_by_coefficients((0,1))
            sage: C.add(N)
            sage: C.list()
            [p-adic node represented by (1, 2) with 9 children,
             p-adic node represented by (2, 1) with 8 children]
            sage: C.complement().list()
            [p-adic node represented by (0, 0) with 9 children,
             p-adic node represented by (1, 0) with 9 children,
             p-adic node represented by (2, 0) with 9 children,
             p-adic node represented by (0, 1) with 9 children,
             p-adic node represented by (1, 1) with 9 children,
             p-adic node represented by (2, 1) with 1 children,
             p-adic node represented by (0, 2) with 9 children,
             p-adic node represented by (2, 2) with 9 children]
        
        .. SEE_ALSO::

            :meth:`pAdicNode.complement`,
            :meth:`pAdicNode.is_full`,
            :meth:`pAdicNode.is_empty`,

        """
        if self.is_full():
            return pAdicNodeCollection(None, pAdics=self.pAdics(),
                                       width=self.width)
        result = pAdicNodeCollection_inverted(None, pAdics=self.pAdics(),
                                              width=self.width)
        for node in self:
            if node.is_full():
                result.remove_by_coefficients(node.coefficients)
            else:
                result.get(node.coefficients).cut(node, from_root=False)
        return result
        
    def permute_coefficients(self, permutation):
        r"""Permute the coefficients of the nodes in this collection.
        
        The permutation will be done in such a way that the i-th entry
        in the new odering will be permutation[i]-th entry of the
        original coefficient.
        
        INPUT:
        
        - ``permutation`` -- a list consisting of the integers 0 to
          the common width of the nodes in this collection (0
          inclusive, width exclusive), which should all appear exactly
          once. The i-th entry of this list should be the index of the
          coefficient each node that should become the i-th
          coefficient after permutation.

        EXAMPLE::

            sage: pAdics = pAdicBase(QQ, 11)
            sage: C = pAdicNodeCollection(None, pAdics=pAdics, width=4)
            sage: C.add(pAdicNode(pAdics=pAdics, coefficients=(1,2,3,4)))
            sage: C.add(pAdicNode(pAdics=pAdics, coefficients=(7,4,1,6)))
            sage: C.add(pAdicNode(pAdics=pAdics, coefficients=(9,2,8,3)))
            sage: C.list()
            [p-adic node represented by (9, 2, 8, 3) with 0 children,
             p-adic node represented by (1, 2, 3, 4) with 0 children,
             p-adic node represented by (7, 4, 1, 6) with 0 children]
            sage: C.permute_coefficients([1,3,2,0])
            sage: C.list()
            [p-adic node represented by (4, 6, 1, 7) with 0 children,
             p-adic node represented by (2, 3, 8, 9) with 0 children,
             p-adic node represented by (2, 4, 3, 1) with 0 children]

        .. SEEALSO::

            :meth:`pAdicNode.permute_coefficients`

        """
        resorted_dict = {}
        for node in self._dict.itervalues():
            node.permute_coefficients(permutation, from_root=False)
            resorted_dict[node.coefficients] = node
        self._dict = resorted_dict
        
    def _increase_width(self, n, pAdics):
        r"""Increase the width of all nodes in this collection.

        INPUT:
        
        - ``n`` -- A non negative integer equal to the number of
          additional coefficients in the new width.

        - ``pAdics`` -- A pAdicBase object that contains the p-adic
          information on which the resulting p-adic nodes should be
          based. This argument should be redundant.

        OUTPUT:

        A pAdicNodeColection containing all nodes with increased width
        that can be made with nodes in this collection.

        .. SEEALSO::

            :meth:`pAdicNode.increase_width`

        """
        result = pAdicNodeCollection(None, pAdics=pAdics, width=self.width+n)
        for cfs in pAdics.representatives(width=n):
            for node in self:
                result.add(node.increase_width(n, pAdics=pAdics,
                                               coefficients=cfs))
        return result
        
    def _decrease_width(self, indices, pAdics):
        r"""Limit the coefficients of nodes in this collection.

        INPUT:
        
        - ``indices`` -- An iterable object containing distinct
          integers between 0 and the common width of nodes in this
          collection (0 inclusive, width exclusive). These are the
          indices of the coefficients that should be present in the
          returned node.

        - ``pAdics`` -- A pAdicBase object that contains the p-adic
          information on which the resulting p-adic nodes should be
          based. This argument should be redundant.

        OUTPUT:

        A pAdicNodeCollection containing all nodes formed by limiting
        the coefficients of nodes in this collection to the given
        indices.

        .. SEEALSO::

            :meth:`pAdicNode.decrease_width`

        """
        result = pAdicNodeCollection(None, pAdics=pAdics, width=len(indices))
        for node in self:
            new_node = node.decrease_width(indices, pAdics=pAdics)
            if result.contains(new_node.coefficients):
                result.get(new_node.coefficients).merge(new_node,
                                                        from_root=False)
            else:
                result.add(new_node)
        return result
        
    def _repr_(self):
        result = "["
        firstLoop = True
        for c in self._dict.itervalues():
            if firstLoop:
                firstLoop = False
            else:
                result += ",\n "
            result += str(c)
        result += "]"
        return result
        
    def _similar_element(self, other, c):
        return (self.contains(c) == other.contains(c) and
                ((c in self._dict and c in other._dict and
                  self._dict[c] == other._dict[c]) or
                 (c in self._dict and c not in other._dict and
                  self._dict[c].is_full()) or
                 (c not in self._dict and c in other._dict and
                  other._dict[c].is_full()) or
                 (c not in self._dict and c not in other._dict)))
                             
    def __eq__(self, other):
        n = self.width
        return (isinstance(other, pAdicNodeCollection) and
                self.pAdics() == other.pAdics() and
                self.size() == other.size() and
                all(self._similar_element(other, c)
                    for c in self.pAdics().representatives(width=self.width)))
        
    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash(tuple(self._dict.itervalues()))
            
class pAdicNodeCollection_inverted(pAdicNodeCollection):
    r"""A collection of p-adic nodes indexed by their coefficients.
    
    A pAdicNodeCollection is a collection of p-adic nodes with the
    same p-adics and width such that no two nodes have the same
    coefficients. Furthermore this collection can be the set of
    children of a node, in which case it also stores the common parent
    of these children. Since the collection might be empty, a
    pAdicNodeCollection stores the common p-adics and width of the
    nodes in the collection as well.

    A pAdicNodeCollection_inverted is a collection of p-adic nodes
    that assumes to contain all possible nodes as full nodes by
    default. These nodes are not actually stored, but only created
    when accessed or modified. This allows the construction of
    infinite p-adic trees that can be described by a finite amount of
    data.

    EXAMPLES::

        sage: pAdics = pAdicBase(ZZ, 3)
        sage: C = pAdicNodeCollection(None, pAdics=pAdics, width=2)
        sage: C.add(pAdicNode(pAdics=pAdics, coefficients=(1, 2)))
        sage: C.add(pAdicNode(pAdics=pAdics, coefficients=(2, 2), full=True))
        sage: C.add(pAdicNode(pAdics=pAdics, coefficients=(0, 1), full=True))
        sage: C.add(pAdicNode(pAdics=pAdics, coefficients=(0, 0)))
        sage: C.list()
        [p-adic node represented by (1, 2) with 0 children,
         p-adic node represented by (0, 1) with 9 children,
         p-adic node represented by (0, 0) with 0 children,
         p-adic node represented by (2, 2) with 9 children]
        sage: C.contains((1, 2))
        True
        sage: C.contains((1, 0))
        False
        sage: C.remove_by_coefficients((0, 0))
        sage: C.list()
        [p-adic node represented by (1, 2) with 0 children,
         p-adic node represented by (0, 1) with 9 children,
         p-adic node represented by (2, 2) with 9 children]
        sage: C.size()
        3
        sage: C.maximal_size()
        9
        sage: C.get((2, 2))
        p-adic node represented by (2, 2) with 9 children
        sage: C.complement().list()
        [p-adic node represented by (0, 0) with 9 children,
         p-adic node represented by (1, 0) with 9 children,
         p-adic node represented by (2, 0) with 9 children,
         p-adic node represented by (1, 1) with 9 children,
         p-adic node represented by (2, 1) with 9 children,
         p-adic node represented by (0, 2) with 9 children,
         p-adic node represented by (1, 2) with 9 children]

    The children of a pAdicNode form a p-adic collection and can be
    used as such::

        sage: pAdics = pAdicBase(ZZ, 2)
        sage: N = pAdicNode(pAdics=pAdics, width=2, full=True)
        sage: isinstance(N.children, pAdicNodeCollection)
        True
        sage: N.children.parent() == N
        True
        sage: N.children.get((1, 0))
        p-adic node represented by (1, 0) with 4 children
        sage: N.children.remove_by_coefficients((0, 1))
        sage: N.children.list()
        [p-adic node represented by (0, 0) with 4 children,
         p-adic node represented by (1, 0) with 4 children,
         p-adic node represented by (1, 1) with 4 children]

    """
    
    def __init__(self, parent, pAdics=None, width=1):
        r"""Initialize a pAdicNodeCollection_inverted.

        When initialized a pAdicNodeCollection_inverted contains all
        possible nodes which are all full.
        
        INPUT:
        
        - ``parent`` -- A pAdicNode that is the common parent of the
          nodes in this collection, or None if no such node exists.

        - ``pAdics`` -- A pAdicBase object or None (default: None),
          giving the shared p-adics of the nodes in this
          collection. If the argument `parent` is not None it will be
          initialized as the p-adics of this parent. Otherwise it is
          not allowed to be None.

        - ``width`` -- A strictly positive integer that is the common
          width among the nodes in this collection. If the argument
          `parent` is not None it will be initialized as the width of
          this parent.

        EXAMPLES::

            sage: pAdics = pAdicBase(QQ, 5)
            sage: pAdicNodeCollection(None, pAdics=pAdics)
            []

        By giving a parent, no other arguments are required::

            sage: pAdics = pAdicBase(ZZ, 7)
            sage: N = pAdicNode(pAdics=pAdics)
            sage: pAdicNodeCollection(N)
            []
            sage: pAdicNodeCollection(None)
            Traceback (most recent call last):
            ...
            ValueError: Should specify pAdics.

        """
        pAdicNodeCollection.__init__(self, parent, pAdics=pAdics, width=width)
        self._removed = []
    
    def add(self, node):
        r"""Add a p-adic node to this collection.
        
        If there already exists a node in this collection with
        the same coefficients as the given node, this function
        will raise an error.
        
        INPUT:
        
        - ``node`` -- A pAdicNode with the same p-adics and width
          as shared among nodes of this collection.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 3)
            sage: R = pAdicNode(pAdics=pAdics, width=2)
            sage: N1 = pAdicNode(pAdics=pAdics, coefficients=(1, 2))
            sage: N2 = pAdicNode(pAdics=pAdics, coefficients=(2, 1))
            sage: N3 = pAdicNode(pAdics=pAdics, coefficients=(2, 1))
            sage: isinstance(R.children, pAdicNodeCollection)
            True
            sage: R.children.add(N1)
            sage: R.children.add(N2)
            sage: R.children.add(N3)
            Traceback (most recent call last):
            ...
            ValueError: A node like p-adic node represented by (2, 1) with 0 children already exists: p-adic node represented by (2, 1) with 0 children
            sage: R.children
            [p-adic node represented by (1, 2) with 0 children,
            p-adic node represented by (2, 1) with 0 children]

        .. SEEALSO::

            :meth:`remove`
            :meth:`remove_by_coefficients`

        """
        self._check_pAdic_node(node)
        if node.coefficients not in self._removed:
            raise ValueError("A node like %s already exists."%(node,))
        self._dict[node.coefficients] = node
        self._removed.remove(node.coefficients)
        if not self.parent() is None:
            node._set_parent(self.parent())
        
    def contains(self, coefficients):
        r"""Check whether this collection contains a node with given
        coefficients.
        
        INPUT:
        
        - ``coefficients`` -- A tuple of numbers that could be the
          label of a p-adic node in this collection, i.e. the length
          of the tuple should equal the common width of the nodes, the
          numbers must be in the number field of the common p-adics of
          the nodes, and they must be representatives of the residue
          field of this common p-adics as returned by the pAdicBase
          object that gives the p-adics.
        
        OUTPUT:

        True, if there exists a node in this collection with
        coefficients equal to the argument `coefficients`. False,
        otherwise.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 5)
            sage: R = pAdicNode(pAdics=pAdics, width=2, full=True)
            sage: R.children.list()[7].remove()
            sage: isinstance(R.children, pAdicNodeCollection)
            True
            sage: R.children.contains((0,0))
            True
            sage: R.children.contains((2,1))
            False

        .. SEEALSO::

            :meth:`pAdicBase.representatives`

        """
        return coefficients not in self._removed
    
    def get(self, coefficients):
        r"""Get a node from this collection by its coefficients.
        
        INPUT:
        
        - ``coefficients`` -- A tuple of numbers that could be the
          label of a p-adic node in this collection, i.e. the length
          of the tuple should equal the common width of the nodes, the
          numbers must be in the number field of the common p-adics of
          the nodes, and they must be representatives of the residue
          field of this common p-adics as returned by the pAdicBase
          object that gives the p-adics.
        
        OUTPUT:

        A pAdicNode object in this collection with coefficients equal
        to the argument `coefficients`. The function will raise an
        error if no such node exists.

        EXAMPLE::

            sage: pAdics = pAdicBase(QQ, 3)
            sage: R = pAdicNode(pAdics=pAdics, width=2, full=True)
            sage: isinstance(R.children, pAdicNodeCollection)
            True
            sage: N = R.children.get((1,2)); N
            p-adic node represented by (1, 2) with 9 children
            sage: N.remove()
            sage: R.children.get((1,2))
            Traceback (most recent call last):
            ...
            ValueError: No node with coefficients (1, 2) exists.

        .. SEEALSO::

            :meth:`pAdicBase.representatives`,
            :meth:`contains`

        """
        if coefficients in self._removed:
            raise ValueError("No node with coefficients " + str(coefficients) +
                             " exists.")
        if coefficients not in self._dict:
            self._dict[coefficients] = pAdicNode(parent=self.parent(),
                                                 coefficients=coefficients,
                                                 full=True, width=self.width,
                                                 pAdics=self.pAdics())
        return self._dict[coefficients]
        
    def remove(self, node):
        r"""Remove a node from this collection
        
        A node is only removed if it was in the collection in the
        first place.
        
        INPUT:
        
        - ``node`` -- A pAdicNode object with the same p-adics and
          with as the common p-adics and width of nodes in this
          collection. If it is in the collection it will be removed
          from the collection.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 2)
            sage: R = pAdicNode(pAdics=pAdics, width=2, full=True)
            sage: isinstance(R.children, pAdicNodeCollection)
            True
            sage: N = R.children.get((1,0))
            sage: R.children.remove(N)
            sage: R.children.list()
            [p-adic node represented by (0, 0) with 4 children,
             p-adic node represented by (0, 1) with 4 children,
             p-adic node represented by (1, 1) with 4 children]

        .. SEEALSO::

            :meth:`add`,
            :meth:`remove_by_coefficients`

        """
        self._check_pAdic_node(node)
        if (node.coefficients in self._dict and
            self._dict[node.coefficients] == node):
            self._dict.pop(node.coefficients)
        if node.coefficients not in self._removed:
            self._removed.append(node.coefficients)
            
    def remove_by_coefficients(self, coefficients):
        r"""Remove the node with given coefficients from this collection.
        
        A node is only removed if a node with the given coefficients
        was in this collection in the first place.
        
        INPUT:
        
        - ``coefficients`` -- A tuple of numbers that could be the
          label of a p-adic node in this collection, i.e. the length
          of the tuple should equal the common width of the nodes, the
          numbers must be in the number field of the common p-adics of
          the nodes, and they must be representatives of the residue
          field of this common p-adics as returned by the pAdicBase
          object that gives the p-adics. The p-adic node with the
          given coefficients will be removed from this collection.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 2)
            sage: R = pAdicNode(pAdics=pAdics, width=2, full=True)
            sage: isinstance(R.children, pAdicNodeCollection)
            True
            sage: R.children.remove_by_coefficients((1, 0))
            sage: R.children.list()
            [p-adic node represented by (0, 0) with 4 children,
             p-adic node represented by (0, 1) with 4 children,
             p-adic node represented by (1, 1) with 4 children]

        .. SEEALSO::

            :meth:`add`,
            :meth:`remove`,
            :meth:`pAdicBase.representatives`

        """
        if coefficients in self._dict:
            self._dict.pop(coefficients)
        if coefficients not in self._removed:
            self._removed.append(coefficients)
            
    def _increase_width(self, n, pAdics):
        r"""Increase the width of all nodes in this collection.

        INPUT:
        
        - ``n`` -- A non negative integer equal to the number of
          additional coefficients in the new width.

        - ``pAdics`` -- A pAdicBase object that contains the p-adic
          information on which the resulting p-adic nodes should be
          based. This argument should be redundant.

        OUTPUT:

        A pAdicNodeColection containing all nodes with increased width
        that can be made with nodes in this collection.

        .. SEEALSO::

            :meth:`pAdicNode.increase_width`

        """
        result = pAdicNodeCollection_inverted(None, pAdics=pAdics,
                                              width=self.width + n)
        for cfs in pAdics.representatives(width=n):
            for cfs0 in self._removed:
                result.remove_by_coefficients(cfs0 + cfs)
            for node in self._dict.itervalues():
                result._dict[coefficients] = node.increase_width(n, pAdics=pAdics,
                                                                 coefficients=cfs)
        return result
        
    def _decrease_width(self, indices, pAdics):
        r"""Limit the coefficients of nodes in this collection.

        INPUT:
        
        - ``indices`` -- An iterable object containing distinct
          integers between 0 and the common width of nodes in this
          collection (0 inclusive, width exclusive). These are the
          indices of the coefficients that should be present in the
          returned node.

        - ``pAdics`` -- A pAdicBase object that contains the p-adic
          information on which the resulting p-adic nodes should be
          based. This argument should be redundant.

        OUTPUT:

        A pAdicNodeCollection containing all nodes formed by limiting
        the coefficients of nodes in this collection to the given
        indices.

        .. SEEALSO::

            :meth:`pAdicNode.decrease_width`

        """
        result = pAdicNodeCollection_inverted(None, pAdics=pAdics,
                                              width=len(indices))
        removal_candidates = []
        for coefficients in self._removed:
            removal_candidates.append(tuple(coefficients[i] for i in indices))
        s = self.pAdics().size_residue_field()^(self.width - len(indices))
        i = 0
        while i < len(removal_candidates):
            c = removal_candidates.count(removal_candidates[i])
            if c == s:
                result.remove_by_coefficients(removal_candidates[i])
            i += c
        for node in self._dict.itervalues():
            new_node = node.decrease_width(indices, pAdics=pAdics)
            if result.contains(new_node.coefficients):
                result.get(new_node.coefficients).merge(new_node,
                                                        from_root=False)
            else:
                result.add(new_node)
        return result
            
    def list(self):
        r"""Give the nodes in this collection as a list.
        
        OUTPUT:

        A list of the nodes in this collection.

        EXAMPLE::

            sage: pAdics = pAdicBase(QQ, 2)
            sage: R = pAdicNode(pAdics=pAdics, width=2, full=True)
            sage: isinstance(R.children, pAdicNodeCollection)
            True
            sage: R.children.list()
            [p-adic node represented by (0, 0) with 4 children,
             p-adic node represented by (1, 0) with 4 children,
             p-adic node represented by (0, 1) with 4 children,
             p-adic node represented by (1, 1) with 4 children]

        """
        result = []
        for c in self.pAdics().representatives(width=self.width):
            if c not in self._removed:
                result.append(self.get(c))
        return result
        
    def __iter__(self):
        for c in self.pAdics().representatives(width=self.width):
            if c not in self._removed:
                yield self.get(c)
    
    def size(self):
        r"""Give the number of nodes in this collection.
        
        OUTPUT:

        A non-negative integer equal to the number of nodes in this
        collection.

        EXAMPLE::

            sage: pAdics = pAdicBase(QQ, 3)
            sage: R = pAdicNode(pAdics=pAdics, width=2, full=True)
            sage: isinstance(R.children, pAdicNodeCollection)
            True
            sage: R.children.size()
            9

        .. SEEALSO::

            :meth:`maximal_size`

        """
        return self.maximal_size() - len(self._removed)
        
    def is_full(self):
        r"""Determine whether this collection is full.

        A collection of p-adic nodes is full if it contains the
        maximal amount of nodes and each node in the collection is
        full.
        
        OUTPUT:

        True, if this collections contains the maximal amount
        of nodes and each node is full. False, otherwise.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 3)
            sage: R = pAdicNode(pAdics=pAdics, full=True)
            sage: isinstance(R.children, pAdicNodeCollection)
            True
            sage: C1 = R.children
            sage: C2 = pAdicNodeCollection(None, pAdics=pAdics)
            sage: C3 = C2.copy()
            sage: C3.add(pAdicNode(pAdics=pAdics))
            sage: C1.is_full()
            True
            sage: C2.is_full()
            False
            sage: C3.is_full()
            False

        .. SEEALSO::

            :meth:`is_empty`,
            :meth:`pAdicNode.is_full`,
            :meth:`maximal_size`

        """
        if len(self._removed) > 0:
            return False
        for node in self._dict.itervalues():
            if not node.is_full():
                return False
        return True
        
    def is_empty(self):
        r"""Determine whether this collection is empty.

        A collection of p-adic nodes is called empty if all the nodes
        in the collection are empty.
        
        OUTPUT:

        True, if each node in this collection is empty. False,
        otherwise.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 3)
            sage: R = pAdicNode(pAdics=pAdics, full=True)
            sage: isinstance(R.children, pAdicNodeCollection)
            True
            sage: C1 = R.children
            sage: C2 = pAdicNodeCollection(None, pAdics=pAdics)
            sage: C3 = C2.copy()
            sage: C3.add(pAdicNode(pAdics=pAdics))
            sage: C1.is_empty()
            False
            sage: C2.is_empty()
            True
            sage: C3.is_empty()
            True

        .. SEEALSO::

            :meth:`is_full`,
            :meth:`pAdicNode.is_empty`

        """
        if self.size() == 0:
            return True
        if self.maximal_size() - len(self._removed) - len(self._dict) > 0:
            return False
        for node in self._dict.itervalues():
            if not node.is_empty():
                return False
        return True
        
    def copy(self):
        r"""Give a copy of this collection.
        
        .. NOTE::

        The copy does not have a parent, since copies of nodes do not.
        
        OUTPUT:

        A pAdicNodeCollection object that contains copies of the nodes
        in this collection.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 3)
            sage: R = pAdicNode(pAdics=pAdics, width=2, full=True)
            sage: isinstance(R.children, pAdicNodeCollection)
            True
            sage: C = R.children.copy()
            sage: C.list()
            [p-adic node represented by (0, 0) with 9 children,
             p-adic node represented by (1, 0) with 9 children,
             p-adic node represented by (2, 0) with 9 children,
             p-adic node represented by (0, 1) with 9 children,
             p-adic node represented by (1, 1) with 9 children,
             p-adic node represented by (2, 1) with 9 children,
             p-adic node represented by (0, 2) with 9 children,
             p-adic node represented by (1, 2) with 9 children,
             p-adic node represented by (2, 2) with 9 children]

        .. SEEALSO::

             :meth:`pAdicNode.copy`

        """
        result = pAdicNodeCollection_inverted(None, pAdics=self.pAdics(),
                                              width=self.width)
        for c in self._removed:
            result.remove_by_coefficients(c)
        for (k,v) in self._dict.iteritems():
            result._dict[k] = v.copy()
        return result
        
    def permute_coefficients(self, permutation):
        r"""Permute the coefficients of the nodes in this collection.
        
        The permutation will be done in such a way that the i-th entry
        in the new odering will be permutation[i]-th entry of the
        original coefficient.
        
        INPUT:
        
        - ``permutation`` -- a list consisting of the integers 0 to
          the common width of the nodes in this collection (0
          inclusive, width exclusive), which should all appear exactly
          once. The i-th entry of this list should be the index of the
          coefficient each node that should become the i-th
          coefficient after permutation.

        EXAMPLE::

            sage: pAdics = pAdicBase(QQ, 11)
            sage: C = pAdicNodeCollection(None, pAdics=pAdics, width=4)
            sage: C.add(pAdicNode(pAdics=pAdics, coefficients=(1,2,3,4)))
            sage: C.add(pAdicNode(pAdics=pAdics, coefficients=(7,4,1,6)))
            sage: C.add(pAdicNode(pAdics=pAdics, coefficients=(9,2,8,3)))
            sage: C.list()
            [p-adic node represented by (9, 2, 8, 3) with 0 children,
             p-adic node represented by (1, 2, 3, 4) with 0 children,
             p-adic node represented by (7, 4, 1, 6) with 0 children]
            sage: C.permute_coefficients([1,3,2,0])
            sage: C.list()
            [p-adic node represented by (4, 6, 1, 7) with 0 children,
             p-adic node represented by (2, 3, 8, 9) with 0 children,
             p-adic node represented by (2, 4, 3, 1) with 0 children]

        .. SEEALSO::

            :meth:`pAdicNode.permute_coefficients`

        """
        pAdicNodeCollection.permute_coefficients(self, permutation)
        resorted_removed = []
        for coefficients in self._removed:
            coefficients = tuple([coefficients[permutation[i]]
                                  for i in range(self.width)])
            resorted_removed.append(coefficients)
        self._removed = resorted_removed
        
    def _repr_(self):
        if self.size() == self.maximal_size():
            return "p-adic node collection excluding no coefficients"
        result = "p-adic node collection excluding coefficients:"
        for c in self._removed:
            result += "\n    " + str(c)
        return result

    def __hash__(self):
        return hash((tuple(self._removed), tuple(self._dict.itervalues())))

class pAdicTree(SageObject):
    r"""A p-adic tree describing possible values of certain variables.

    A pAdicTree consists of a number of variables given by their names
    and a p-adic tree giving the possible p-adic values these
    variables can attain. The names of the variables are stored as
    strings and the p-adic tree is stored by storing a pAdicNode that
    is the root of the tree.

    A pAdicTree is considered to be immutable. Therefore every
    non-hidden method will not modify the underlying tree structures,
    but first make copies instead. This may however be very slow for
    certain applications and hence a user is adviced with p-adic nodes
    instead if one does not want to save the original tree.

    This class contains certain set like operations to be performed on
    them. Note that for all these operations the variables are taken
    into account, in the sense that possible values are linked to
    their respective variable. If one combines two pAdicTrees with
    different variables the result will be a pAdicTree with variables
    equal to the union of the variables in both trees.
    
    EXAMPLES:

    Manipulating the variables in a p-adic tree::

        sage: T = pAdicTree(('a', 'b'), prime=3); T
        p-adic tree for the variables ('a', 'b') with respect to p-adics given by Rational Field and (3)
        sage: T.add_variable('c')
        p-adic tree for the variables ('a', 'b', 'c') with respect to p-adics given by Rational Field and (3)
        sage: T.remove_variable('b')
        p-adic tree for the variables ('a',) with respect to p-adics given by Rational Field and (3)
        sage: T.reorder_variables(('b', 'a'))
        p-adic tree for the variables ('b', 'a') with respect to p-adics given by Rational Field and (3)
        sage: T.change_variables_to(('a', 'c'))
        p-adic tree for the variables ('a', 'c') with respect to p-adics given by Rational Field and (3)

    Set like operations on p-adic trees::

        sage: pAdics = pAdicBase(ZZ, 2)
        sage: N1 = pAdicNode(pAdics=pAdics, width=2, full=True)
        sage: N1.children.remove_by_coefficients((0, 0))
        sage: N2 = N1.copy()
        sage: T1 = pAdicTree(('x','y'), root=N1)
        sage: T2 = pAdicTree(('y','z'), root=N2)
        sage: T = T1.union(T2); T
        p-adic tree for the variables ('x', 'y', 'z') with respect to p-adics given by Rational Field and (2)
        sage: ls, I = T.give_as_congruence_condition(); ls
        [(0, 0, 1), (0, 1, 0), (0, 1, 1), (1, 0, 0), (1, 0, 1), (1, 1, 0), (1, 1, 1)]
        sage: I
        Principal ideal (2) of Integer Ring
        sage: T = T1.intersection(T2); T
        p-adic tree for the variables ('x', 'y', 'z') with respect to p-adics given by Rational Field and (2)
        sage: ls, I = T.give_as_congruence_condition(); ls
        [(0, 1, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0), (1, 1, 1)]
        sage: I
        Principal ideal (2) of Integer Ring
        sage: T = T1.difference(T2); T
        p-adic tree for the variables ('x', 'y', 'z') with respect to p-adics given by Rational Field and (2)
        sage: ls, I = T.give_as_congruence_condition(); ls
        [(1, 0, 0)]
        sage: I
        Principal ideal (2) of Integer Ring
        sage: T = T1.complement(); T
        p-adic tree for the variables ('x', 'y') with respect to p-adics given by Rational Field and (2)
        sage: ls, I = T.give_as_congruence_condition(); ls
        [(0, 0)]
        sage: I
        Principal ideal (2) of Integer Ring
    
    ..SEEALSO:
        
        :class: pAdicNode
    """
    
    def __init__(self, variables, prime=None, ring=None, pAdics=None,
                 root=None, full=True):
        r"""Initialize this pAdicTree.
        
        INPUT:
        
        - ``variables`` -- A non-empty iterable object containing the
          names that should be used for the variables of this
          tree. Each name should be a string. In case of a single
          variable this may also be just the name of that variable.

        - ``prime`` -- A prime ideal (default: pAdics.prime_ideal())
          that defines the p-adics of this p-adic tree. Will be
          ignored if the argument pAdics is defined.

        - ``ring`` -- A ring (default: prime.ring()) that can be used
          to define a pAdicBase object. Will be ignored if pAdics is
          defined.

        - ``pAdics`` -- A pAdicBase object (default: root.pAdics() or
          pAdicBase(ring, prime) if root is not given) that defines
          the p-adics to be used by this tree.

        - ``root`` -- A pAdicNode object or None (default:None) that
          is the root of some p-adic tree with the same p-adics as
          this tree and width equal to the number of variables. If set
          to None, will be initialized as the full or empty node with
          these properties depending on the argument `full`.

        - ``full`` -- A boolean value (default: True), that determines
          whether the default value of the argument root is a full
          node (True) or an empty node (False).

        EXAMPLES::

            sage: pAdicTree('x', prime=3)
            p-adic tree for the variables ('x',) with respect to p-adics given by Rational Field and (3)
            sage: pAdicTree(('a', 'b', 'c'), prime=2)
            p-adic tree for the variables ('a', 'b', 'c') with respect to p-adics given by Rational Field and (2)
            sage: pAdicTree(('x1', 'x2'), prime=3, ring=QuadraticField(-1))
            p-adic tree for the variables ('x1', 'x2') with respect to p-adics given by Number Field in a with defining polynomial x^2 + 1 and (3)

        The difference between full and empty::

            sage: T = pAdicTree('x', prime=2, full=True)
            sage: T.is_full()
            True
            sage: T = pAdicTree('x', prime=2, full=False)
            sage: T.is_empty()
            True

        Using a custom node to initialize the tree::

            sage: pAdics = pAdicBase(QQ, 7)
            sage: N = pAdicNode(pAdics=pAdics, width=2, full=True)
            sage: T = pAdicTree(('x', 'y'), root=N)
            sage: T
            p-adic tree for the variables ('x', 'y') with respect to p-adics given by Rational Field and (7)

        """
        if not hasattr(variables, '__iter__'):
            variables = [variables]
        self._variables = tuple(str(v) for v in variables)
        width = len(variables)
        
        if root is None:           
            if pAdics is None:
                if prime is None:
                    raise ValueError("At least the argument prime must be set")
                prime = Ideal(prime)
                if ring is None:
                    ring = prime.ring()
                pAdics = pAdicBase(ring, prime)
            root = pAdicNode(pAdics=pAdics, full=full, width=width)
        self._root = root
        
        if width != self._root.width:
            raise ValueError("The width must be equal to that of the root")
                                               
    def _repr_(self):
        return (("p-adic tree for the variables %s "%(self._variables,)) +
                ("with respect to %s"%self.pAdics()))
    
    def root(self):
        r"""Give the root of this tree.

        .. NOTE::
        
        To make sure the internal structure of the tree can not be
        modified, this returns a copy of the root rather than the root
        itself.
        
        OUTPUT:
        
        A copy of the unique level 0 node in this p-adic tree.

        EXAMPLE::

            sage: T = pAdicTree(('x', 'y'), prime=3)
            sage: T.root()
            p-adic node represented by (0, 0) with 9 children

        """
        return self._root.copy()
        
    def nodes_at_level(self, level):
        r"""Give a list of the nodes in this tree at a certain level.

        NOTE:

        Will return the nodes as part of a tree that is a copy of the
        one stored in this pAdicTree, to prevent accidental
        modification of the internal structure of this tree. Since
        this tree only exists as long as its root does, the root is
        also given.
        
        INPUT:
        
        - `level` -- A non-negative integer that is the level at which
          we want to get the nodes.
          
        OUTPUT:
        
        A tuple consisting of: a list of copies of all nodes at level
        `level` that are in this tree; and the root of the tree that
        contains those nodes.

        EXAMPLE::

            sage: T = pAdicTree(('x', 'y'), prime=2)
            sage: ls, Tc = T.nodes_at_level(2); ls
            [p-adic node represented by (0, 0) with 4 children,
             p-adic node represented by (2, 0) with 4 children,
             p-adic node represented by (0, 2) with 4 children,
             p-adic node represented by (2, 2) with 4 children,
             p-adic node represented by (1, 0) with 4 children,
             p-adic node represented by (3, 0) with 4 children,
             p-adic node represented by (1, 2) with 4 children,
             p-adic node represented by (3, 2) with 4 children,
             p-adic node represented by (0, 1) with 4 children,
             p-adic node represented by (2, 1) with 4 children,
             p-adic node represented by (0, 3) with 4 children,
             p-adic node represented by (2, 3) with 4 children,
             p-adic node represented by (1, 1) with 4 children,
             p-adic node represented by (3, 1) with 4 children,
             p-adic node represented by (1, 3) with 4 children,
             p-adic node represented by (3, 3) with 4 children]
        
        ..SEEALSO:
        
            :func:`pAdicNode.children_at_level`

        """
        T = self.root()
        return T.children_at_level(level), T
        
    def pAdics(self):
        r"""Return the p-adics corresponding to the p-adic tree.
        
        OUTPUT:

        The pAdicBase object that gives the p-adics of the p-adic tree
        in this object.

        EXAMPLE::

            sage: T = pAdicTree('a', prime=11)
            sage: T.pAdics()
            p-adics given by Rational Field and (11)

        """
        return self._root.pAdics()
                
    def variables(self):
        r"""Give the variables associated to this p-adic tree.
        
        OUTPUT:
        
        A tuple of names of the variables associated to this
        tree.

        EXAMPLE::

            sage: T = pAdicTree(('a1','a2','a3','a4'), prime=2)
            sage: T.variables()
            ('a1', 'a2', 'a3', 'a4')

        """
        return self._variables
        
    def add_variable(self, *variables):
        r"""Add one or multiple variables to this tree.
        
        Will construct a new tree that is the same as this one, but
        with any new variables given added. Any given variable will
        only be added if it did not already exist in the current
        tree. The order of the newly added variables will remain the
        same. Newly added variables will be assumed to attain any
        possible value.
        
        INPUT:
        
        Any number of arguments, each of which is the name of a
        variable to be added to this tree. Each name should be a
        string.

        OUTPUT:
  
        A pAdicTree such that: Each variable in this pAdicTree is in
        the new pAdicTree in the same order; Each variable of the ones
        given is in this new pAdicTree and the once which were not
        already in this tree are at the end in the same order; Each
        variable is assumed to attain the same values as in this tree
        and all possible values if it was not part of this tree.

        EXAMPLE::

            sage: T = pAdicTree(('x','y'), prime=3); T
            p-adic tree for the variables ('x', 'y') with respect to p-adics given by Rational Field and (3)
            sage: T.add_variable('z')
            p-adic tree for the variables ('x', 'y', 'z') with respect to p-adics given by Rational Field and (3)
            sage: T.add_variable('a', 'b')
            p-adic tree for the variables ('x', 'y', 'a', 'b') with respect to p-adics given by Rational Field and (3)
            sage: T.add_variable('x', 'z')
            p-adic tree for the variables ('x', 'y', 'z') with respect to p-adics given by Rational Field and (3)

        .. SEEALSO::

            :meth:`remove_variable`,
            :meth:`reorder_variables`,
            :meth:`change_variables_to`

        """
        new_variables = list(self.variables())
        count = 0
        for var in variables:
            if var not in new_variables:
                count += 1
                new_variables.append(var)
        return pAdicTree(variables=new_variables,
                         root=self.root().increase_width(count))
        
    def remove_variable(self, *variables):
        r"""Remove one or multiple variables from this tree.
        
        Will return a tree that is this tree with all the given
        variables removed from them. Variables are only removed if
        they were part of this tree to begin with. The order of the
        remaining variables will be the same as in this tree.
        
        The nodes in this tree will be changed accordingly, assuming
        that removing these variables corresponds to removing the
        corresponding coefficients in the nodes. Multiple nodes with
        the same coefficients will be merged.
        
        INPUT:
        
        Any number of arguments, each of which is the name of a
        variable. Each name should be a string.

        OUTPUT:

        A pAdicTree containing only those variables of this tree that
        were not given as an argument. All these variables attain the
        values for which there is an assignment of values in this tree
        with the same value for these variables.

        EXAMPLE::

            sage: T = pAdicTree(('a','b','c','d'), prime=5); T
            p-adic tree for the variables ('a', 'b', 'c', 'd') with respect to p-adics given by Rational Field and (5)
            sage: T.remove_variable('c')
            p-adic tree for the variables ('a', 'b', 'd') with respect to p-adics given by Rational Field and (5)
            sage: T.remove_variable(['a', 'd'])
            p-adic tree for the variables ('b', 'c') with respect to p-adics given by Rational Field and (5)

        .. SEEALSO::

            :meth:`add_variable`,
            :meth:`reorder_variables`,
            :meth:`change_variables_to`

        """
        all_variables = self.variables()
        variables_to_keep = list(all_variables)
        for var in variables:
            if var in variables_to_keep:
                variables_to_keep.remove(var)     
        indices = [all_variables.index(var) for var in variables_to_keep]
        return pAdicTree(variables=variables_to_keep,
                         root=self.root().decrease_width(indices))
        
    def reorder_variables(self, variables):
        r"""Reorder the variables in this tree.

        Give a pAdicTree with the same variables as in this tree,
        except that the ordering is the same as the ordering given.

        INPUT:

        - ``variables`` -- An iterable object, containing the names of
          the variables in this tree exactly once and ordered in the
          preferred ordering.

        OUTPUT:

        A pAdicTree with as variables those given in the same order as
        they are given. These variables are given the same values as
        they had in this tree.

        EXAMPLE::

            sage: T = pAdicTree(('a','b','c'), prime=5); T
            p-adic tree for the variables ('a', 'b', 'c') with respect to p-adics given by Rational Field and (5)
            sage: T.reorder_variables(('b', 'c', 'a'))
            p-adic tree for the variables ('b', 'c', 'a') with respect to p-adics given by Rational Field and (5)

        .. SEEALSO::

            :meth:`add_variable`,
            :meth:`remove_variable`,
            :meth:`change_variables_to`

        """
        if not hasattr(variables, '__iter__'):
            variables = [variables]
        variables = list(variables)
        myvars = self.variables()
        if not len(variables) == len(myvars):
            raise ValueError("The given number of variables (" +
                             str(len(variables)) + ") is not the same as " +
                             "the number of variables as this tree (" +
                             str(len(myvars)) + ")")
        try:
            permutation = [myvars.index(variables[i])
                           for i in range(self._root.width)]
        except ValueError:
            raise ValueError("The variables " + str(variables) + " and " +
                             str(myvars) + " do not correspond 1 to 1")
        root = self.root()
        root.permute_coefficients(permutation)
        return pAdicTree(variables=variables, root=root)
        
    def change_variables_to(self, variables, ignore_order=False):
        r"""Change the variables to a given set of variables.

        Performs the actions of adding, removing and reordering
        variables to obtain a pAdicTree with variables matching the
        given argument variables.

        INPUT

        - ``variables`` -- An iterable object of names of
          variables. These are the variables the final tree should
          have in the order it should have them. Each name should be a
          string.

        - ``ignore_order`` -- A boolean (default: False)
          indicating whether the order of the variables
          should be ignored.

        OUTPUT:

        A pAdicTree containing precisely the variables given, which
        attain those values for which there are values of the
        variables in this tree for which corresponding variables have
        the same value.

        If the argument `ignore_order` was set to True the variables
        can be in any order. Otherwise they will be in the order as
        given.

        EXAMPLE::

            sage: T = pAdicTree(('a1','b1','c1'), prime=2); T
            p-adic tree for the variables ('a1', 'b1', 'c1') with respect to p-adics given by Rational Field and (2)
            sage: T.change_variables_to(('b1', 'b2', 'b3'))
            p-adic tree for the variables ('b1', 'b2', 'b3') with respect to p-adics given by Rational Field and (2)

        .. SEEALSO::

            :meth:`add_variable`,
            :meth:`remove_variable`,
            :meth:`reorder_variables`

        """
        if not hasattr(variables, '__iter__'):
            variables = [variables]
        variables = tuple(variables)
        varSet = Set(variables)
        myVarSet = Set(self.variables())
        removeSet = myVarSet - varSet
        result = self
        if removeSet.cardinality() > 0:
            result = result.remove_variable(*removeSet)
        addSet = varSet - myVarSet
        if addSet.cardinality() > 0:
            result = result.add_variable(*addSet)
        if not ignore_order and result.variables() != variables:
            result = result.reorder_variables(variables)
        return result

    def is_empty(self):
        r"""Tell whether this tree is empty.

        A p-adic tree is called empty if its root is empty, i.e. if
        there is no infinite paths from the root. This is equivalent
        to the variables taking on no values.

        OUTPUT:

        True if there exist no infinite paths in this tree, False
        otherwise.

        EXAMPLE::

            sage: T = pAdicTree('x', prime=2)
            sage: T1 = pAdicTree('x', prime=2)
            sage: T2 = pAdicTree('y', prime=2, full=False)
            sage: N = pAdicNode(pAdics=T2.pAdics())
            sage: N.children.add(pAdicNode(pAdics=T2.pAdics(), coefficients=(1,), full=True))
            sage: T3 = pAdicTree('z', root=N)
            sage: T1.is_empty()
            False
            sage: T2.is_empty()
            True
            sage: T3.is_empty()
            False
        
        .. SEEALSO::

            :meth:`is_full`,
            :meth:`pAdicNode.is_empty`

        """
        return self._root.is_empty()

    def is_full(self):
        r"""Tell whether this tree is full.

        A p-adic tree is called full if its root is full, i.e. if
        every possible infinite path from the root exists. This is
        equivalent to the variables taking on every possible value.

        OUTPUT:

        True if all possible infinite paths exist in this tree, False
        otherwise.

        EXAMPLE::

            sage: T = pAdicTree('x', prime=2)
            sage: T1 = pAdicTree('x', prime=2)
            sage: T2 = pAdicTree('y', prime=2, full=False)
            sage: N = pAdicNode(pAdics=T2.pAdics())
            sage: N.children.add(pAdicNode(pAdics=T2.pAdics(), coefficients=(1,), full=True))
            sage: T3 = pAdicTree('z', root=N)
            sage: T1.is_full()
            True
            sage: T2.is_full()
            False
            sage: T3.is_full()
            False

        .. SEEALSO::

            :meth:`is_empty`,
            :meth:`pAdicNode.is_full`

        """
        return self._root.is_full()

    @cached_method
    def get_values_at_level(self, level):
        r"""Give the values in this tree at a given level.

        Will give a list of tuples containing all the possible values
        for the variables modulo $P^n$, where $P$ is the prime of the
        corresponding p-adics and $n$ is the given level. In each
        tuple the i-th value corresponds to the i-th variable of this
        tree.

        INPUT:

        - ``level`` -- A non-negative integer.

        OUTPUT:

        A list which contains for each node at the given level its
        representative.

        EXAMPLE::

            sage: T = pAdicTree(('x', 'y'), prime=2)
            sage: T.get_values_at_level(2)
            [(0, 0),
             (0, 1),
             (0, 2),
             (0, 3),
             (1, 0),
             (1, 1),
             (1, 2),
             (1, 3),
             (2, 0),
             (2, 1),
             (2, 2),
             (2, 3),
             (3, 0),
             (3, 1),
             (3, 2),
             (3, 3)]

        .. SEEALSO::

            :meth:`pAdicNode.representative`

        """
        result = [node.representative()
                  for node in self._root.children_at_level(level)]
        result.sort()
        return result

    @cached_method
    def give_as_congruence_condition(self):
        r"""Give the possible values of the variables as a congruence
        condition.

        Since we can only store a finite amount of information, each
        p-adic tree must have a level at which all nodes are
        full. Therefore we can express the possible values of the
        variables by a number of congruence classes modulo a big
        enough power of the prime associated with the p-adics.

        OUTPUT:

        A tuple consisting of: A list of tuples containing the
        possible values of the variables modulo some ideal $I$; and
        the ideal $I$. Note that for each tuple in the list the i-th
        value corresponds to the i-th variable in this tree.

        EXAMPLE::

            sage: pAdics = pAdicBase(QQ, 2)
            sage: N = pAdicNode(pAdics=pAdics, width=2, full=True)
            sage: N.children.remove_by_coefficients((1, 0))
            sage: T = pAdicTree(('a', 'b'), root=N)
            sage: ls, I = T.give_as_congruence_condition(); ls
            [(0, 0), (0, 1), (1, 1)]
            sage: I
            Principal ideal (2) of Integer Ring

        .. SEE_ALSO::

            :meth:`get_values_at_level`

        """
        m = self._root.minimum_full_level()
        modulus = self.pAdics().prime_ideal()^m
        return self.get_values_at_level(m), modulus
        
    def _check_similar_tree(self, other):
        r"""Check whether two trees have the same pAdics.

        Throws an error if the other object is not a pAdicTree with
        the same p-adics.

        INPUT:

        - ``other`` -- Some object.

        """
        if not isinstance(other, pAdicTree):
            raise ValueError("The argument %s is not a pAdicTree."%(other,))
        if self.pAdics() != other.pAdics():
            raise ValueError("The two trees don't have the same pAdics.")
        
    def _get_similar_trees(self, other):
        r"""Turn two p-adic trees into trees with the same variables.

        INPUT:

        - ``other`` - A pAdicTree with the same p-adics as this tree.

        OUTPUT:

        A tuple of pAdicTree's with the same variables and pAdics. The
        variables are the union of the variables in this tree and the
        given tree. The values for the variables in the first tree
        corresond to the values for the variables in this tree, whilst
        the values for the variables in the second tree correspond to
        the values for the variables in the given tree.

        """
        self._check_similar_tree(other)
        variables = list(self.variables())
        for var in other.variables():
            if var not in variables:
                variables.append(var)
        return (self.change_variables_to(variables),
                other.change_variables_to(variables))
        
    def copy(self):
        r"""Make a copy of this pAdicTree.

        OUTPUT:

        A pAdicTree that contains the same variables and values as
        this pAdicTree.

        EXAMPLE::

            sage: T = pAdicTree(('a', 'b'), prime=5); T
            p-adic tree for the variables ('a', 'b') with respect to p-adics given by Rational Field and (5)
            sage: T.copy()
            p-adic tree for the variables ('a', 'b') with respect to p-adics given by Rational Field and (5)

        """
        return pAdicTree(variables=self.variables(), root=self.root())
        
    def union(self, other):
        r"""Give the union of two p-adic trees.

        The union of two p-adic trees is a p-adic tree with as
        variables the union of the variables of the two p-adic
        trees. Furthermore a tuple of values for these variables is in
        the union if and only if at least one of the trees has a tuple
        of values for its variables wherein each common variable with
        the union has the same value.

        INPUT:

        - ``other`` -- A pAdicTree using the same p-adics as this
          pAdicTree.

        OUTPUT:

        A pAdicTree that is the union of this p-adic tree and the
        given p-adic tree.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 2)
            sage: N1 = pAdicNode(pAdics=pAdics, width=2, full=True)
            sage: N1.children.remove_by_coefficients((0, 0))
            sage: N2 = N1.copy()
            sage: T1 = pAdicTree(('x','y'), root=N1)
            sage: T2 = pAdicTree(('y','z'), root=N2)
            sage: T = T1.union(T2); T
            p-adic tree for the variables ('x', 'y', 'z') with respect to p-adics given by Rational Field and (2)
            sage: ls, I = T.give_as_congruence_condition(); ls
            [(0, 0, 1), (0, 1, 0), (0, 1, 1), (1, 0, 0), (1, 0, 1), (1, 1, 0), (1, 1, 1)]
            sage: I
            Principal ideal (2) of Integer Ring

        .. SEE_ALSO::

            :meth:`intersection`,
            :meth:`difference`,
            :meth:`complement`

        """
        T1, T2 = self._get_similar_trees(other)
        T = T1.root()
        T.merge(T2.root())
        return pAdicTree(variables=T1.variables(), root=T)
        
    def intersection(self, other):
        r"""Give the intersection of two p-adic trees.

        The intersection of two p-adic trees is a p-adic tree with as
        variables the union of the variables of the two p-adic
        trees. Furthermore a tuple of values for these variables is in
        the intersection if and only if both trees have a tuple of
        values for its variables wherein each common variable with the
        intersection has the same value.

        INPUT:

        - ``other`` -- A pAdicTree using the same p-adics as this
          pAdicTree.

        OUTPUT:

        The pAdicTree that is the intersection of this p-adic tree and
        the given p-adic tree.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 2)
            sage: N1 = pAdicNode(pAdics=pAdics, width=2, full=True)
            sage: N1.children.remove_by_coefficients((0, 0))
            sage: N2 = N1.copy()
            sage: T1 = pAdicTree(('x','y'), root=N1)
            sage: T2 = pAdicTree(('y','z'), root=N2)
            sage: T = T1.intersection(T2); T
            p-adic tree for the variables ('x', 'y', 'z') with respect to p-adics given by Rational Field and (2)
            sage: ls, I = T.give_as_congruence_condition(); ls
            [(0, 1, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0), (1, 1, 1)]
            sage: I
            Principal ideal (2) of Integer Ring

        .. SEE_ALSO::

            :meth:`union`,
            :meth:`difference`,
            :meth:`complement`

        """
        T1, T2 = self._get_similar_trees(other)
        T = T1.root()
        T.limit_to(T2.root())
        return pAdicTree(variables=T1.variables(), root=T)
        
    def difference(self, other):
        r"""Gives the difference of this tree and another.

        The difference of a p-adic tree with another p-adic tree is a
        p-adic tree with as variables the union of the variables of
        the two p-adic trees. Furthermore a tuple of values for these
        variables is in the difference if and only if the first tree
        has a tuple of values for its variables wherein each common
        variable with the difference has the same value, and the
        second tree does not have such a tuple.

        INPUT:

        - ``other`` -- A pAdicTree using the same p-adics as this
          pAdicTree.

        OUTPUT:

        The pAdicTree that is the difference of this p-adic tree and
        the given p-adic tree.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 2)
            sage: N1 = pAdicNode(pAdics=pAdics, width=2, full=True)
            sage: N1.children.remove_by_coefficients((0, 0))
            sage: N2 = N1.copy()
            sage: T1 = pAdicTree(('x','y'), root=N1)
            sage: T2 = pAdicTree(('y','z'), root=N2)
            sage: T = T1.difference(T2); T
            p-adic tree for the variables ('x', 'y', 'z') with respect to p-adics given by Rational Field and (2)
            sage: ls, I = T.give_as_congruence_condition(); ls
            [(1, 0, 0)]
            sage: I
            Principal ideal (2) of Integer Ring

        .. SEE_ALSO::

            :meth:`union`,
            :meth:`intersection`,
            :meth:`complement`

        """
        T1, T2 = self._get_similar_trees(other)
        T = T1.root()
        T.cut(T2.root())
        return pAdicTree(variables=T1.variables(), root=T)
        
    def complement(self):
        r"""Give the complement of this p-adic tree.

        The complement of a p-adic tree is the difference of a full
        p-adic tree with the same variables and p-adics and that tree.

        OUTPUT:

        A pAdicTree that is the complement of this p-adic tree.

        EXAMPLE::

            sage: pAdics = pAdicBase(ZZ, 2)
            sage: N1 = pAdicNode(pAdics=pAdics, width=2, full=True)
            sage: N1.children.remove_by_coefficients((0, 0))
            sage: T1 = pAdicTree(('x','y'), root=N1)
            sage: T = T1.complement(); T
            p-adic tree for the variables ('x', 'y') with respect to p-adics given by Rational Field and (2)
            sage: ls, I = T.give_as_congruence_condition(); ls
            [(0, 0)]
            sage: I
            Principal ideal (2) of Integer Ring

        .. SEE_ALSO::

            :meth:`union`,
            :meth:`intersection`,
            :meth:`difference`

        """
        return pAdicTree(variables=self.variables(),
                         root=self.root().complement())

    def _cache_key(self):
        return self.variables(), self._root

    def __eq__(self, other):
        return (isinstance(other, pAdicTree) and
                self.variables() == other.variables() and
                self._root == other._root)
