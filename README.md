The factor package
=================

The [factor package][] is a [Haskell][] library for factoring integers
and polynomials, implementing the following algorithms:

- [Number field sieve](doc/nfs-example.txt) for factoring arbitrary integers
- [Elliptic curve method](doc/ecm-example.txt) for finding "small" factors of integers
- Miller-Rabin probabilistic primality test for integers
- Berlekamp-Zassenhaus algorithm for factoring integer polynomials
- Berlekamp algorithm for factoring polynomials over GF(*p*) (for small primes *p*)
- Cantor–Zassenhaus algorithm for factoring polynomials over GF(*p*) (for arbitrary odd primes *p*)

This software is released under the [MIT License](LICENSE).

Install
-------

Installing the factor package requires [cabal][]:

    git clone https://github.com/gilith/factor.git
    cd factor
    cabal install --enable-tests

The factor package contains an executable called `factor`, which is
[run](doc/factor-usage.txt) as follows:

    Usage: factor [options] "expression to factor"
          --trial=N       Set trial division maximum to N
          --ecm-primes=N  Limit ECM to first N primes (use - for no limit)
          --nfs-chars=N   Use N quadratic characters in NFS
          --nfs-verbose   Show complete lists in NFS verbose messages
      -v  --verbose       Enable verbose messages
      -t  --timestamp     Prepend verbose messages with timestamp
          --version       Print version
      -h  --help          Show help

Example input expressions:

      2047               Concrete integer
      2^2^7 + 1          Integer expression
      N[100]             Random 100-bit positive integer
      P[50] * P[50]      Product of random 50-bit primes
      x^4 - 10*x^2 + 1   Polynomial over the integers
      x^5^2 - x (mod 5)  Polynomial over GF(5)

Let expressions are supported: `let p = P[4] in x^p - x (mod p)`  
Multivariate polynomials (e.g., `y^2 - x^3 - a*x - b`) are not supported

Test and Profile
----------------

Use [cabal][] to run the test suite:

    cabal test

Profiles of the time and memory requirements for factoring inputs of
various sizes:

- [Number field sieve profile](doc/nfs-profile.txt)
- [Elliptic curve method profile](doc/ecm-profile.txt)

The following recipe can be used to [visualize the dynamic memory
usage](doc/nfs-memory.png) of the number field sieve:

    cabal clean
    cabal configure --enable-profiling
    cabal build
    factor +RTS -hc -RTS -v --ecm-primes 0 'P[35] * P[35]'
    hp2ps -e8in -c factor.hp
    gm convert -density 180 factor.ps factor.png
    xview factor.png

References
----------

Comments in the code contain references to descriptions of the
specific implemented algorithms, and the following references helped
with general understanding of the number field sieve:

- [A Tale of Two Sieves][Pomerance1996], Carl Pomerance, 1996
- [The Number Field Sieve][Byrnes2005], Steven Byrnes, 2005
- [An Introduction to the General Number Field Sieve][Briggs1998], Matthew E Briggs, 1998
- [Integer Factorization][Jensen2005], Per Leslie Jensen, 2005
- [Square Root Algorithms for the Number Field Sieve][Thome2012], Emmanuel Thome, 2012
- [MSIEVE: A Library for Factoring Large Integers][msieve], Jason Papadopoulos, 2010

[Briggs1998]: https://vtechworks.lib.vt.edu/bitstream/handle/10919/36618/etd.pdf "An Introduction to the General Number Field Sieve"
[Byrnes2005]: https://wstein.org/129-05/final_papers/Steve_Byrnes.pdf "The Number Field Sieve"
[cabal]: https://www.haskell.org/cabal/ "Cabal"
[factor package]: https://hackage.haskell.org/package/factor "factor package"
[Haskell]: https://www.haskell.org/ "Haskell"
[Jensen2005]: http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.693.9784 "Integer Factorization"
[msieve]: https://github.com/radii/msieve "msieve"
[Pomerance1996]: https://www.ams.org/notices/199612/pomerance.pdf "A Tale of Two Sieves"
[Thome2012]: https://hal.inria.fr/hal-00756838/en "Square root algorithms for the number field sieve"
