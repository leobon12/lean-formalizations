import QuantumZipper.Proofs.Thm18.G4WeldRound

/-!
# Theorem 1.8, node G4: the group law, opposite signs

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (2), cases
`s, t` of opposite signs with `s + t ≠ 0` (no separate proof in the paper). **Own elementary
arguments** (driver algebra: Brownian scaling and reverse-flow concatenation, as in
`G4WeldGroup`, `G4WeldGroupUp`, `G4WeldRound`). Write `c = (x, W)`, `τ_ℓ`, `a_ℓ` for the
unzipping time and scale of `ℓ`.

* `t < 0 < s`, `s < −t` (`DownShortData`): `Z_s` re-zips part of what `Z_t` unzipped, along
  `backDrv`, the time reversal of `W` on `[τ_{m}, τ_ℓ]` (`ℓ = −t`, `m = ℓ − s`), scaled by `a_ℓ`.
* `t < 0 < s`, `s > −t` (`DownLongData`): `Z_s` re-zips all of it and then zips `m = s + t`
  more along the driver `q` of `c` (`backCatDrv`).
* `s < 0 < t`, `−s < t` (`UpShortData`): `Z_{−ℓ}` unzips the last part of the zip `Z_t`; the
  length-`m` driver `q` of `c` is `p` restricted to `[0, T_q]`.
* `s < 0 < t`, `−s > t` (`UpLongData`): `Z_{−ℓ}` unzips all of `Z_t` and `m = ℓ − t` more of `c`.

In each case the field-level facts (driver is a good length-welding driver, scale and time
relations, `RegEq` of the fields) are the data; the drivers of the two sides then agree exactly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-! ## `t < 0 < s`, `s < −t` -/

/-- Time reversal of `W` on `[τ', τ]`, scaled by `a`. -/
def backDrv (W : ℝ → ℝ) (τ τ' a : ℝ) : ℝ × (ℝ → ℝ) :=
  ((τ - τ') / a ^ 2, fun u => (W (τ - a ^ 2 * u) - W τ) / a)

/-! ## `t < 0 < s`, `s > −t` -/

/-- Time reversal of `W` on `[0, τ]` (scaled by `a`) followed by the `a`-rescaled driver `q`. -/
def backCatDrv (W : ℝ → ℝ) (τ a : ℝ) (q : ℝ × (ℝ → ℝ)) : ℝ × (ℝ → ℝ) :=
  (τ / a ^ 2 + q.1 / a ^ 2, fun u =>
    if u ≤ τ / a ^ 2 then (W (τ - a ^ 2 * u) - W τ) / a else (W 0 - W τ + q.2 (a ^ 2 * u - τ)) / a)

end Thm18Asm
end QuantumZipper
