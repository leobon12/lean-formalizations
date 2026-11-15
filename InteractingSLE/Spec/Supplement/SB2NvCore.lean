/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JvV5

/-!
# SB2(2): the v5 admissibility clause asks for drivenness on the zero stages (finding, deterministic core)

Packet PROVE-GW2-GEOM2, round 10 (D28: `StageOK` measurability and `PieceRegular (EL j)`, taken off
PROVE-SB2-LIFTSET's list). `Lk.StageOK ρ G Z` ends with `∀ ω ∈ G, IsDrivenCurve (ρ ω)`. The v5 rule
(`Lk.GeomFactsV5At`) uses `G = Gd` and the curve `Lk.mρ Gd (lρ3 …) j F`, which is `lρ3 … j F ω` on the whole of `Gd`,
zero events included. At a stage whose actual piece has lifetime `0` that curve is constant, and a constant curve is not
driven:

* **`not_isDrivenCurve_const`**: the capacity clock of a constant curve does not increase;
* **`stCurvep_zero_life`**, **`not_isDrivenCurve_stCurvep_zero`**: a stage curve of lifetime `0` is constant;
* **`not_isDrivenCurve_cρ3_of_life_zero`**: away from stage `0`, a v3/v4 stage curve whose actual driver has lifetime
  `0` is not driven;
* **`not_stageOK_v5_of_life_zero`**: hence the v5 admissibility clause fails at any stage `j ≠ 0` and any `ω ∈ Gd` whose
  actual driver at instruction `j + relOff` has lifetime `0`.

At an odd stage, instruction `j + relOff` is a connector (`relOff_even`). Connectors do not read their driver, and
neither `IsStagedHistory` nor `StagedPiecesRegular` constrains it. Setting it to the lifetime-`0` driver keeps every
hypothesis of `Lf.SB2LowerSetting` and falsifies the clause on `Gd`, which `GeomAt4` forces to contain almost every
sample with a nontrivial root. The corrected rule (v6, `SB2NvRule`) masks the curve to the nontrivial launched stages.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Nv

open Lk Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

/-- **A constant curve is not driven**: its capacity clock is constant. -/
theorem not_isDrivenCurve_const (z : ℂ) : ¬ IsDrivenCurve (fun _ : ℝ => z) := by
  intro h
  obtain ⟨-, -, -, -, hmono, -, -⟩ := h.localDriver 1 one_pos
  have h01 : capClock (fun _ : ℝ => z) 0 = capClock (fun _ : ℝ => z) 1 := by
    unfold capClock
    rw [(nonempty_Icc.2 le_rfl).image_const, (nonempty_Icc.2 zero_le_one).image_const]
  exact (hmono ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ one_pos).ne h01

/-- A stage curve of lifetime `0` is constant. -/
theorem stCurvep_zero_life (c : Chart) (m : ℝ) (p : ℝ≥0 → ℂ) (s₂ : ExplState) :
    stCurvep c m p 0 s₂ = fun _ => stValp c m p 0 s₂ 0 := by
  funext u
  rw [stCurvep_of_fin (by simp : (0 : ℝ≥0∞) ≠ ⊤)]
  simp [clockOf]

/-- **A stage curve of lifetime `0` is not driven.** -/
theorem not_isDrivenCurve_stCurvep_zero (c : Chart) (m : ℝ) (p : ℝ≥0 → ℂ) (s₂ : ExplState) :
    ¬ IsDrivenCurve (stCurvep c m p 0 s₂) := by
  rw [stCurvep_zero_life]
  exact not_isDrivenCurve_const _

/-- **Away from stage `0`, a v3/v4 stage curve whose actual driver has lifetime `0` is not driven.** -/
theorem not_isDrivenCurve_cρ3_of_life_zero {Ω : Type*} (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ)
    (J₂ : Finset ℝ) (R : ℝ) (c : Chart) (m : ℝ) (D₁ : Ω → ℕ → Drv) {j : ℕ} (hj : j ≠ 0) (F : ℕ → Ω → Drv) (ω : Ω)
    (h0 : (D₁ ω (j + relOff κ θ b₁ J₁ R (D₁ ω))).2 = 0) :
    ¬ IsDrivenCurve (cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ j F ω) := by
  unfold cρ3
  rw [cΦ3_of_ne κ θ b₁ J₁ R c m D₁ hj ω, h0]
  exact not_isDrivenCurve_stCurvep_zero _ _ _ _

/-- **The v5 admissibility clause fails at a zero-lifetime stage `j ≠ 0` on `Gd`.** -/
theorem not_stageOK_v5_of_life_zero {Ω : Type*} [MeasurableSpace Ω] (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ)
    (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (R : ℝ) (c : Chart) (m : ℝ) (D₁ : Ω → ℕ → Drv) {Gd : Set Ω}
    (Z : Set Ω) {j : ℕ} (hj : j ≠ 0) (F : ℕ → Ω → Drv) {ω : Ω} (hω : ω ∈ Gd)
    (h0 : (D₁ ω (j + relOff κ θ b₁ J₁ R (D₁ ω))).2 = 0) :
    ¬ StageOK (mρ Gd (cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁) j F) Gd Z := by
  intro h
  have hd := h.2.2.2 ω hω
  rw [mρ_of_mem hω] at hd
  exact not_isDrivenCurve_cρ3_of_life_zero κ θ b₁ J₁ b₂ J₂ R c m D₁ hj F ω h0 hd

end InteractingSLE.Theorem14.SB.Nv
