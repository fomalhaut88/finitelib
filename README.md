# finitelib

`finitelib` is a library for advanced maths over finite groups, fields,
their extensions, multiprecision operations and related things.

At the moment the library supports:
* Finite groups
* Finite fields (prime - `GF(p)`, splitting - `GF(p^m)`, binary - `GF(2^m)`, Montgomery representation)
* Euclidean rings (including modular operations)
* Polynomials
* Multiprecision operations over unsigned integers
    * Converting
    * Formatting
    * Basic operations: addition, subtraction, product, division, bitwise operations
    * Prime numbers: Fetmat test, Miller-Rabin test, Legendre symbol, Tonelli–Shanks algorithm
