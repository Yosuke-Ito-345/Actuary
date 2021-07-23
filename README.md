# Actuary

This is an experimental package where the basic part of actuarial mathematics is formalized using the Coq Proof Assistant.

## Description of files
- all_Actuary: This file imports all the related libraries: Basics, Interest, LifeTable, Premium, Reserve.
- Basics: Some basic facts of mathematics are collected for the main part of the package.
- Interest: The theory of interest is formalized, including the present and future values of annuities.
- LifeTable: The life table is defined axiomatically, and is examined mainly from probability theory.
- Premium: Basic actuarial notations are introduced, including various facts on the present values of annuities, insurance and so on.
- Reserve: The level premium reserve is defined, and some useful formulas are also proved formally.
- Examples: Some applications of this package are shown.

## Notice
- This package uses MathComp and Coquelicot.
- Classical logic is assumed.
- The axiom of choice is used.
- The following functions are set to be coercions:
  - INR : nat >-> R
  - IZR : Z >-> R
- The infix notation "^" is redefined as Rpower, and the original function pow is represented as ".^".
- The future updates of this package may not be backward compatible.
- Any advice or comment is welcome.

## Main changes from version 1.0 to version 2.0
- Inequalities ">" and ">=" are replaced with "<" and "<=" (advice from ZulipChat).
- The force of mortality is formalized.
- Notations "δ", "ω" are changed to "\δ", "\ω" respectively.
- Some basic lemmas are taken in the "auto" tactic by "Hint Resolve".
- Generalized the frequency of payments in Premium.v. and Reserve.v.
- The continuous payment case is newly formalized.
