# Reflected random walk with spatial singularities

Accompanying Lean source for the geometric-topology revision of *An invariance principle for reflected random walk on cell configurations with spatial singularities* (24 September 2026):

- [Exact statements and definitions](../../ReflectedGMS/GeomTop/Statement.lean).
- [Harmonic-coordinate and invariance-principle proofs](../../ReflectedGMS/GeomTop/Theorems.lean).
- [Current AI research paper](https://github.com/leobon12/ai-generated-mathematics/blob/main/papers/reflected-random-walks.pdf).

The proof declarations are `ReflectedGMS.GeomTop.geomHarmonicCoordinateMainTheorem` and `ReflectedGMS.GeomTop.geomReflectedInvarianceMainTheorem`. The source files and their transitive dependencies were already present in this public repository as dependencies of the GMS release; this guide exposes their direct entrypoints.

## Mathematical scope

The environments are unmarked planar cell configurations with a closed singular-set witness of zero one-dimensional Hausdorff measure. The assumptions include local finiteness away from that set, line connectivity off a common witness on a measurable probability-one set, mass transport modulo translations and positive dilations, and the diameter–conductance moment. The invariance principle additionally assumes ergodicity modulo scaling.

The conclusions provide finite-specific-energy harmonic coordinates with uniformly sublinear corrector and a reflected invariance principle for the area clock and deterministic holding-time clock, with deterministic positive-definite Brownian covariance.

## Revision correspondence

The Lean source names the earlier geometric-topology revision's Theorems 1.2 and 1.3. The current 40-page PDF numbers the corresponding results 1.4 and 1.5, adds an explicit pathwise witness convention, and revises its averaging argument. This is a link to the accompanying formalization, **not a claim that every change in the current PDF has been separately formalized or that the two formulations are definitionally identical**. The removed whole-plane variant is not the source linked here.

## Verification

With this repository's pinned Lean and Mathlib versions:

```sh
lake exe cache get
lake build ReflectedGMS.GeomTop.Theorems
lake env lean results/reflected-gms/Check.lean
```

The check verifies exact statement types, absence of `sorry`, and dependencies on the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
