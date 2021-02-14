# Actuary

This is an experimental package where the basic part of actuarial mathematics is formalized using the Coq Proof Assistant.

## Description of files
- Basics: Some basic facts of mathematics are collected for the main part of the package.
- Interest: The theory of interest is formalized, including the present and future values of annuities.
- LifeTable: The life table is defined axiomatically, and is examined mainly from probability theory.
- Premium: Basic actuarial notations are introduced, including various facts on the present values of annuities, insurance and so on.
- Reserve: The level premium reserve is defined, and some useful formulas are also proved formally.
- Examples: Some applications of this package are shown.

## Notice
- This package uses MathComp and Coquelicot.
- Classical logic is assumed.
- The following functions are set to be coercions:
  - INR : nat >-> R
  - IZR : Z >-> R
- The infix notation "^" is redefined as Rpower, and the original function pow is represented as ".^".
- This package may be frequently updated, and may not be backward compatible.
- Any advice or comment is welcome.

