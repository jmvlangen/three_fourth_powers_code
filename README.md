# Code for the article: _On the sum of fourth powers in arithmetic progression_

This git repository contain files required to perform the
computational part of the article: _On the sum of fourth powers in
arithmetic progression_.

## Contents

* **src** Code written for Sage to perform various computations on Frey curves

* **load.sage** A script to load all the Sage code into sage.

* **computations.rst** A file that contains all the computations that
  verify the various claims throughout the paper. The computations can
  be verified using Sage's doc-test system (see _How to use_)
  
* **save\_nfs.m** Some magma code to save newforms to the file format
  specified in _src/modular\_forms/newform wrapper.sage_.
  
* **generate\_nfs.m** A magma script that will compute the newforms
  used in the paper and save them to the files used by _computations.rst_.
  
* **README.md** This file

## Requirements

To run the code, the user needs to have an installation of MAGMA and
SageMath, both available through the command line. The code has been
tested in MAGMA version 2.24-8 and SageMath version 8.7, so the same
or newer version is recommended. It is known that a bug in SageMath
version 8.4 breaks the code.

If you want to test the computations in _computations.rst_ make sure
you have the files _E1.nfs_ and _E2.nfs_ in a new directory called
_tmp_ inside this directory. These files can be obtained by extracting
them from ... or by running the _generate\_nfs.m_ magma script. The
latter can be done by opening a terminal inside this directory and
typing

``shell
>> magma generate_nfs.m
``

Note that generating these files will take a long time (about a week)
and is therefore not recommended.

## How to use

### Checking the computations

The file _computations.rst_ contains all the computations needed for
the paper. The file is written in reStructuredText and can be opened
with any text editor. The file contains fragments of code, written as
the input on the Sage command line followed by the corresponding
output, if any. Some text surrounding these fragments explains what is
computed in each part.

All the output in the document can be checked using SageMath's
doc-test system. Simply open a terminal in the current directory and
type

``shell
>> sage -t -T 0 -m 0 computations.rst
``

The additional arguments are required, since the computations exceed
the standard time and memory limits of Sage's doc-tests.

After some hours the doc-test should print "All tests passed" and
finish, in which case all the output in the document has been
verified.

### Using the code

In order to use the Sage code and work with Frey curves and other
tools developed for this paper, start a Sage terminal in this
directory and type

``shell
sage: load('load.sage')
``

which will load all the code from the _src_ directory. Note that the
paths in _load.sage_ are relative and thus require the sage terminal
to be in this directory to work.
