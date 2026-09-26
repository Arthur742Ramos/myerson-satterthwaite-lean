# Myerson-Satterthwaite Theorem (Lean 4 Formalization)

Formalizes the continuous-type Myerson-Satterthwaite impossibility theorem for bilateral trading (Myerson and Satterthwaite, 1983): no mechanism can simultaneously be ex post efficient (almost surely), Bayesian incentive compatible, interim individually rational, and budget balanced when the buyer and seller type supports overlap.

The model: buyer values and seller costs lie in real compact intervals with overlap; type distributions are atomless full-support probability measures — each type measure dominates the Lebesgue measure restricted to its interval, so every nonempty open subset of the interval has positive probability (no density requirement is imposed). Allocation `q` takes values in `[0,1]` and is measurable; interim trade probabilities and utilities are Bochner integrals of sections. The proof uses payoff equivalence (envelope identities for interim utilities), the fact that efficiency identifies the allocation almost everywhere, the layer-cake identity for the efficient surplus `S`, and the strict rent-gap inequality `B + C > S`, which together force an accounting contradiction.

## Toolchain

Lean and Mathlib v4.35.0-rc2.

## Build

Run `lake update` once, then run `lake build`.

## License

BSD-3-Clause.
