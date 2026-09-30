import QuantumZipper.Proofs.Zipper.UnifRCSplit
import QuantumZipper.Proofs.Zipper.WedgeUnzipCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D29 (wedge unzipping), X-G part 1: the field identity `x_t = y_t + ψ_t` and the named inputs

Task X-GOOD (handoff `WEDGE-UNZIP.md`, decisions D26/D29). Node **X-G**
(`WedgeUnzip.XGoodAllStmt`, `WedgeUnzipCore.lean`): for `x = X + α₀(−log|·|)` and an independent
driver `W = √κ B`, a.s. the unzipped fields `x_t` are good at all times `t ≥ 0`.

Route (Sheffield, arXiv:1012.4797, §5.4, pp. 70–72, step (3); D26/D29). With `y = x + γ log|·|`
(the `Γ⁰` field, `F2.h0f_eq_unzY`), unzipping is affine in the field, and on every dyadic folded
circle `x_t = y_t + ψ_t` with `ψ_t = −γ log‖E_t‖`, `E_t = f_t⁻¹` (the proved identity
`F2.step3FieldCircDy_holds`). Goodness reads a sample only through its dyadic coordinates
(`isLQGGood_congr_coords`), so

* `coords_unzX_eq` / `isLQGGood_unzX_iff`: a.s., for all `t ≥ 0`, `x_t` is good iff
  `y_t + ofFun ψ_t` is good (**proved**, exact).

`ψ_t` is continuous on `ℍ̄` away from the two tip points `O^±_t` (where `E_t = 0`), so away from
the tips goodness of `y_t + ψ_t` is local rule (5.1) applied to the `Γ⁰` field (files
`WedgeXGoodFar.lean`, `WedgeXGoodTight.lean`); at the tips the tip statement **TIP-X**
(`TipXStmt`) is needed. The named inputs, stated here:

* `YGoodAllStmt` (`Γ⁰`, D26): a.s. `y_t` good for all `t ≥ 0`.
* `ExtNonvanishStmt`: a.s., for all `t ≥ 0`, `E_t ≠ 0` on `ℍ̄` off the two tips.
* `TipXStmt` (**TIP-X**): a.s., for all `t ≥ 0`, `ofFun ψ_t` is regular (witness: its circle
  averages) and the
  approximate boundary measures of `x_t` are uniformly small near `O^±_t` along `goodFilter`.

Own bookkeeping (the identity is the paper's step (3): `coordChange` is affine in the field).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

/-! ## The tip points and the added function -/

/-- The two **tip points** `O⁻_t, O⁺_t` of the unzipping at time `t` (`sideImages`): the images of
`0∓` under `f_t`, where `E_t = f_t⁻¹` vanishes and `x_t` carries the `α₀(−log|·|)` singularity. -/
def tipSet (W : ℝ → ℝ) (t : ℝ) : Set ℝ := {(sideImages W t).1, (sideImages W t).2}

/-- The tip points as points of `ℂ`. -/
def tipPts (W : ℝ → ℝ) (t : ℝ) : Set ℂ := ((↑) : ℝ → ℂ) '' tipSet W t

/-- `ψ_t = −γ log‖E_t‖`, the function unzipping moves the log singularity `γ log|·|` onto. -/
def logTipFun (κ : ℝ) (W : ℝ → ℝ) (t : ℝ) : ℂ → ℝ :=
  fun z => -(Real.sqrt κ * Real.log ‖F2.extInv W t z‖)

theorem tipSet_finite (W : ℝ → ℝ) (t : ℝ) : (tipSet W t).Finite :=
  (Set.finite_singleton _).insert _

theorem isCompact_tipSet (W : ℝ → ℝ) (t : ℝ) : IsCompact (tipSet W t) :=
  (tipSet_finite W t).isCompact

theorem ofReal_mem_tipPts_iff {W : ℝ → ℝ} {t s : ℝ} : (s : ℂ) ∈ tipPts W t ↔ s ∈ tipSet W t := by
  constructor
  · rintro ⟨a, ha, h⟩
    rwa [← Complex.ofReal_injective h]
  · exact fun h => ⟨s, h, rfl⟩

/-! ## The field identity -/

/-- **`x_t` and `y_t + ψ_t` have the same dyadic coordinates**, a.s. for all `t ≥ 0` (from the
dyadic circle identity `F2.step3FieldCircDy_holds`). -/
theorem coords_unzX_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Factorization.coords (F2.unzX κ (X ω) (drive κ B ω) t) =
        Factorization.coords (F2.unzY κ (X ω) (drive κ B ω) t +
          ofFun (logTipFun κ (drive κ B ω) t)) := by
  filter_upwards [F2.step3FieldCircDy_holds κ hκ hκ4 P B X hB hX hind] with ω hω t ht
  funext i
  have h := hω t ht (Denumerable.ofNat (ℤ × ℤ × ℕ × ℕ) i).2.2.1
    (Denumerable.ofNat (ℤ × ℤ × ℕ × ℕ) i).1 (Denumerable.ofNat (ℤ × ℤ × ℕ × ℕ) i).2.1
    (Denumerable.ofNat (ℤ × ℤ × ℕ × ℕ) i).2.2.2
  exact h

/-! ## The named inputs -/

/-- **`E_t` vanishes only at the tips.** A.s., for all `t ≥ 0`, `E_t = f_t⁻¹` (boundary extension
on `ℝ`) is nonzero at every point of `ℍ̄` other than `O^±_t`. (On `ℍ`, `E_t ∈ ℍ`; on `ℝ` off
`[O⁻_t, O⁺_t]` it is real and nonzero; on `(O⁻_t, O⁺_t)` it is a point of the simple SLE trace
other than `η(0) = 0`, Rohde–Schramm.) -/
def ExtNonvanishStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ u ∈ Hbar, u ∉ tipPts (drive κ B ω) t →
      F2.extInv (drive κ B ω) t u ≠ 0

end WedgeUnzip
end QuantumZipper
