The factor package
=================

The [factor package][] is a [Haskell][] library for factoring positive
integers into prime powers.

This software is released under the [MIT License][].

Install
-------

Installing the factor package requires [cabal][]:

    git clone https://github.com/gilith/factor.git
    cd factor
    cabal install --enable-tests

Test
----

Use [cabal][] to run the test suite:

    cabal test

Run
----

The factor package contains an executable called factor, which is run
as follows:

    Usage: factor N
    where N is the positive integer to be factored

[Briggs1998]: https://vtechworks.lib.vt.edu/bitstream/handle/10919/36618/etd.pdf "An Introduction to the General Number Field Sieve"
[Byrnes2005]: https://wstein.org/129-05/final_papers/Steve_Byrnes.pdf "The Number Field Sieve"
[cabal]: https://www.haskell.org/cabal/ "Cabal"
[factor package]: https://hackage.haskell.org/package/factor "factor package"
[Haskell]: https://www.haskell.org/ "Haskell"
[Jensen2005]: http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.693.9784 "Integer Factorization"
[MIT License]: https://github.com/gilith/factor/blob/master/LICENSE "MIT License"
[msieve]: https://github.com/radii/msieve "msieve"
[Pomerance1996]: https://www.ams.org/notices/199612/pomerance.pdf "A Tale of Two Sieves"
[Thome2012]: https://hal.inria.fr/hal-00756838/en "Square root algorithms for the number field sieve"
