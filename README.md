# Myerson-Satterthwaite Theorem (Lean 4 Formalization)

This project aims to formalize the Myerson-Satterthwaite impossibility theorem for bilateral trading: no mechanism can be simultaneously ex post efficient, Bayesian incentive compatible, interim individually rational, and budget balanced. The formalization uses the finite-discrete-type version, with finite value and cost sets, probability mass functions (PMFs), and finite-sum expectations.

## Toolchain

Lean and Mathlib v4.35.0-rc2.

## Build

Run `lake update` once, then run `lake build`.

## License

BSD-3-Clause.
