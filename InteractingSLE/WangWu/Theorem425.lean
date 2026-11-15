/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Prop418Det
import InteractingSLE.WangWu.Theorem18

/-!
# Wang–Wu Theorem 4.25 from determination of the frozen couplings

Packet PROVE-WW-B9. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), Theorem 4.25 (text
dump L1871–1876): "For every finite collection of force points and weights, the `SLE₄(ρ_L; ρ_R)` hull coupled with the
GFF by the full stopping-time kernel of Definition 1.5 is determined by that GFF up to its continuation threshold `T`.
If `T = 0`, the assertion concerns only the initial state."

The consumers of Theorem 4.25 (`WangWu.Bridge`) need only `LP.WWTheorem17Statement`, determination for the couplings with
the frozen optional hull specification at `κ = 4`. Astra's §D.2 (Aux. 52–55, ruling R38) proves that statement from the
two-seed input (`wwTheorem17Statement_of_twoSeed`, `Prop418Det.lean`), without Wang–Wu's force-point induction. Conversely,
`WWTheorem425Statement` itself follows from `LP.WWTheorem17Statement` and the continuity of Wang–Wu Theorem 1.8
(`LP.WWTheorem18Statement`):

* **`wwTheorem425Statement_of_wwTheorem17`**: a full level-line coupling with an admissible seed and a continuous trace
  is an optional hull coupling (Corollary 3.9, `IsFullLevelLineCoupling.isOptionalHullCoupling`), so it is determined by
  `LP.WWTheorem17Statement`; at an inadmissible seed the lifetime is `0` and the history is the initial state.
* **`wwTheorem425Statement_of_twoSeed`**: the same from the two-seed input, the local extensions and Theorem 1.8;
* **`twoSeedGraphInput_four`**: the two-seed input `LP.TwoSeedGraphInput 4` splits into determination of the two-seed
  couplings and the continuous trace of the boundary-hitting two-seed words (`Theorem18.TwoSeedHittingStatement 4`,
  weights in `(−2, 0)`); the nonnegative weights have their trace already (`isCompleteForceWord_twoSeed_of_admissible`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu

/-- **At an inadmissible seed the killed history is field-determined**: the lifetime is `0` almost surely, so the
constant map `Ψ = (0, 0, 0, 0)` reads it off any field. -/
theorem isFieldDeterminedHistory_of_thresholdCondition {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {a : ℝ} (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hth : ForceWord.ThresholdCondition ρL ρR 0 xL xR) (F : Ω → LQGMetric.DistOn upperHalfPlaneOpens) :
    LP.IsFieldDeterminedHistory P F W VL VR ζ := by
  refine ⟨fun _ => (0, 0, 0, 0), measurable_const, ?_⟩
  filter_upwards [hE.2.2.2.2] with ω hp
  have hζ := IsIntegratedSLEPath.lifetime_eq_zero_of_threshold hp hth
  refine ⟨hζ.symm, fun t ht => ?_⟩
  rw [hζ] at ht
  exact absurd ht (not_lt.2 bot_le)

/-- **Wang–Wu Theorem 4.25** (`WWTheorem425Statement`) from determination of the frozen `κ = 4` couplings
(`LP.WWTheorem17Statement`) and the continuous trace of Wang–Wu Theorem 1.8 (`LP.WWTheorem18Statement`). -/
theorem wwTheorem425Statement_of_wwTheorem17 (h17 : LP.WWTheorem17Statement.{u})
    (h18 : LP.WWTheorem18Statement.{u}) : WWTheorem425Statement.{u} := by
  intro nL nR xL xR ρL ρR hxF Ω mΩ P _ 𝓕 W VL VR B ζ F hF
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · exact isFieldDeterminedHistory_of_thresholdCondition hF.1 hseed F
  · refine h17 xL xR ρL ρR hxF P 𝓕 W VL VR B ζ F (hF.isOptionalHullCoupling ?_ hseed)
    filter_upwards [h18 xL xR ρL ρR hxF P 𝓕 W VL VR B ζ hF.1] with ω hω
    obtain ⟨η, hη, -⟩ := hω
    exact ⟨η, hη⟩

/-- **Wang–Wu Theorem 4.25 from the two-seed input** (Wang–Wu Proposition 4.24 as `LP.TwoSeedGraphInput 4`), the local
extensions of Aux. 53 + 55 at `κ = 4`, and the continuity of Wang–Wu Theorem 1.8. -/
theorem wwTheorem425Statement_of_twoSeed (h2 : LP.TwoSeedGraphInput.{u} 4)
    (hext : Determination.LocalExtensionStatement.{u} 4) (h18 : LP.WWTheorem18Statement.{u}) :
    WWTheorem425Statement.{u} :=
  wwTheorem425Statement_of_wwTheorem17 (wwTheorem17Statement_of_twoSeed h2 hext) h18

/-- **The two-seed input at `κ = 4`, split** (Wang–Wu Proposition 4.24): determination of every two-seed coupling with
weights `> −2`, and the continuous trace of the boundary-hitting two-seed words (`Theorem18.TwoSeedHittingStatement 4`);
the two-seed words with nonnegative weights have their trace by Lemma 4.12 / Corollary 4.13. -/
theorem twoSeedGraphInput_four
    (hdet : ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      LP.HasFieldDeterminedHistories.{u} 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR))
    (hhit : Theorem18.TwoSeedHittingStatement.{u} 4) : LP.TwoSeedGraphInput.{u} 4 := by
  intro rL rR hL hR
  refine ⟨hdet rL rR hL hR, fun P _ 𝓕 W VL VR B ζ hE => ?_⟩
  have hc : LP.IsCompleteForceWord.{u} 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) :=
    Theorem18.twoSeedComplete_of_hitting (by norm_num) le_rfl hhit rL rR hL hR
  filter_upwards [hc P 𝓕 W VL VR B ζ hE] with ω hω
  obtain ⟨η, hη, -⟩ := hω
  exact ⟨η, hη⟩

end InteractingSLE.WangWu
