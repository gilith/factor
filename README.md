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

[cabal]: https://www.haskell.org/cabal/ "Cabal"
[Haskell]: https://www.haskell.org/ "Haskell"
[factor package]: https://hackage.haskell.org/package/factor "factor package"
[MIT License]: https://github.com/gilith/factor/blob/master/LICENSE "MIT License"
