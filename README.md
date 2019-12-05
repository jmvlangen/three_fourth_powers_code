# Code for the article: _On the sum of fourth powers in arithmetic progression_

This git repository contains files related to the computational part
of the article: [_On the sum of fourth powers in arithmetic
progression_](https://arxiv.org/abs/1907.12351). It contains
documented Sage code for working with Frey curves, Q-curves and
Frey-Q-curves as well as the corresponding newforms. Furthermore the
file _computations.sage_ gives all the details for the computations
done in the mentioned article. It consists of code snippets combined
with explanatory notes to make the computations insightful.

## Contents

* **calculations.rst** A structured file giving all the computations
  needed for the article accompanied by explanatory notes. This file
  explains in detail what computations have to be done, the input that
  has to be provided to compute this and the corresponding output. The
  output can be automatically verified using Sage's doc-test system
  (see _How to use_)

* **src** A folder containing code written for Sage to perform various
  computations on Frey curves, Q-curves and Diophantine equations. An
  effort has been made to document the code according to the Sage
  guidelines for developers.

* **load.sage** A script to load all the Sage code into Sage.
  
* **save\_nfs.m** Some MAGMA code to save newforms to the file format
  specified in _src/modular\_forms/newform wrapper.sage_.
  
* **generate\_nfs.m** A magma script that will compute the newforms
  used in the paper and save them to the files used by _calculations.rst_.
  
* **README.md** This file

## Requirements

To use the code the user needs an installation of
[SageMath](http://www.sagemath.org/) version 8.4 or newer.  The code
was last tested on version 8.7.

The code has an option to compute newforms using MAGMA. For this one
needs an installation of
[MAGMA](http://magma.maths.usyd.edu.au/magma/). The code has been
tested on version 2.24-8 so that version or a newer one is
recommended. The installation should be set up such that it is
accessible through SageMath's [MAGMA
interface](http://doc.sagemath.org/html/en/reference/interfaces/sage/interfaces/magma.html).

If you want to test the computations in _calculations.rst_make sure
you have an installation of MAGMA as described before. Furthermore you
need a directory in this directory called _tmp_ that contains the
files _E1.nfs_ and _E2.nfs_ containing the newform data needed for the
computations. These files can be generated using the _generate\_nfs.m_
magma script. This script can be executed using the _load_ command
from within a magma terminal or directly by opening a terminal inside
this directory and typing

    >> magma generate_nfs.m

Note that generating these files will take a long time (about a week)
and is therefore not recommended. Pre-computed versions of these files
are available upon request.

## How to use

### Checking the computations

The file _calculations.rst_ contains all the computations needed for
the paper. The file is written in reStructuredText and can be opened
with any text editor. The file contains fragments of code, written as
the input on the Sage command line followed by the corresponding
output, if any. Some text surrounding these fragments explains what is
computed in each part.

All the output in the document can be checked using SageMath's
doc-test system. Simply open a terminal in the current directory and
type

    >> sage -t -T 0 -m 0 calculations.rst

The additional arguments are required, since the computations exceeds
the standard time and memory limits of Sage's doc-tests.

After some hours the doc-test should print "All tests passed" and
finish, in which case all the output in the document has been
verified.

### Using the code

In order to use the Sage code and work with Frey curves and other
tools developed for this paper, start a Sage terminal in this
directory and type

    sage: load('load.sage')

which will load all the code from the _src_ directory. Note that the
paths in _load.sage_ are relative and thus require the sage terminal
to be in this directory to work.
