# Actuary

This is an experimental package where the basic part of actuarial mathematics is formalized using the Coq Proof Assistant.

## Requirements

- [Coq 8.17.1](https://coq.inria.fr/download) or later
- [Mathematical Components 1.17.0 to 1.19.0](https://math-comp.github.io) 
- [Coquelicot 3.4.0](https://gitlab.inria.fr/coquelicot/coquelicot) or later

## Building and installation instructions

The easiest way to install the latest released version
is via [opam](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-actuary
```

To instead build and install manually, do:

```shell
git clone https://github.com/Yosuke-Ito-345/Actuary.git
cd Actuary
make   # or make -j <number-of-cores-on-your-machine>
make install
```

## Description of files in theories directory

- `all_Actuary.v`: This file imports all theory modules defined by files below: `Basics`, `Interest`, `LifeTable`, `Premium`, `Reserve`.
- `Basics.v`: Some basic facts of mathematics are collected for the main part of the package.
- `Interest.v`: The theory of interest is formalized, including the present and future values of annuities.
- `LifeTable.v`: The life table is defined axiomatically, and is examined mainly from probability theory.
- `Premium.v`: Basic actuarial notations are introduced, including various facts on the present values of annuities, insurance and so on.
- `Reserve.v`: The level premium reserve is defined, and some useful formulas are also proved formally.
- `Examples.v`: Some applications of this package are shown.

## Notice

- Classical logic is assumed.
- The axiom of choice is used.
- The following functions are set to be coercions:
  - `INR : nat >-> R`
  - `IZR : Z >-> R`
- The infix notation `^` is redefined as `Rpower`, and the original function `pow` is represented as `.^`.
- The future updates of this package may not be backward compatible.
- Any advice or comment is welcome.

## Main changes from version 1.0 to version 2.0

- Inequalities `>` and `>=` are replaced with `<` and `<=` (advice from Zulip Chat).
- The force of mortality is formalized.
- Notations `δ`, `ω` are changed to `\δ`, `\ω`, respectively.
- Some basic lemmas are taken in the `auto` tactic by `Hint Resolve`.
- Generalized the frequency of payments in `Premium.v` and `Reserve.v`.
- The continuous payment case is newly formalized.
