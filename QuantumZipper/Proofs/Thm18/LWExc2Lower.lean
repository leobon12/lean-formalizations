import QuantumZipper.Proofs.Thm18.LWExcUpper

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, LW-FAR route: the lower half of Lawler–Werness Lemma 4.3, limit step

`lw43Lower_of_key`: `LW43LowerStmt` follows from
* `HarmReflectStmt` — the reflection principle for harmonic functions (L. Ahlfors, *Complex
  Analysis*, 3rd ed. 1979, Ch. 4 §6.5, Theorem 24, p. 172, for `Ω` a disk centred on `ℝ`;
  `literature/Ahlfors_ComplexAnalysis_1979.pdf`, PDF p. 187), used to show that the limit
  `∂_y h(x) = lim h(x + iy)/y` defining `yDer` exists at every `x ≥ 0`;
* `LW43KeyLowerStmt` — the lower half of LW's key estimate `h_η(z) ≍ Im z · diam η/(|z| + 1)²`
  (`Re z ≥ 0`), G. F. Lawler, B. M. Werness, Ann. Probab. 41 (2013), sketch of proof of
  Lemma 4.3, p. 24 (`literature/1011.3551.pdf`).

This is LW's own reduction (p. 24: "In fact we get an estimate `∂_y h_η(x) ≍ diam/(x + 1)²`. The
key estimate used here is ..."), with the existence of `∂_y h` made explicit.
-/

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- **Reflection principle for harmonic functions**, local form (Ahlfors, Thm 24, p. 172, with
`Ω = B(x, r)`; only a smaller disk `B(x, ρ)` is kept): `v` harmonic in the upper half-disk,
continuous up to the diameter and `0` there, has a harmonic extension to a disk about `x`. -/
def HarmReflectStmt : Prop :=
  ∀ (v : ℂ → ℝ) (x r : ℝ), 0 < r → InnerProductSpace.HarmonicOnNhd v (H ∩ ball (x : ℂ) r) →
    ContinuousOn v (Hbar ∩ ball (x : ℂ) r) → (∀ z ∈ ball (x : ℂ) r, z.im = 0 → v z = 0) →
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ∃ V : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd V (ball (x : ℂ) ρ) ∧
      EqOn V v (Hbar ∩ ball (x : ℂ) ρ)

end LWFar
end Thm18Asm
end QuantumZipper
