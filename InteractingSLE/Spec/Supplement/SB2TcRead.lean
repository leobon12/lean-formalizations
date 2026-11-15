/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvLineAbs

/-!
# Readings of the upper flow from SB2(1)'s line marks

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half). The clock, the relative driver and the trace of the
version are read from the physical line marks `D.absMarks T` (the retained past and the killed histories of the
capped upper flows through `max(T, T_n)`). The basic readings:

* `measurable_coord_ruleMarks` (generic): a path coordinate at a rational time below the rule is a mark of the rule;
* `measurable_coord_iterMarks`: the same for the iterated union's marks;
* **`EntranceUnion.measurable_ηc_absMarks`**: the capped flow `η_n` at every rational time `q ≤ T` is
  `D.absMarks T`-measurable.

Deterministic in the data; nothing here replaces a source statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Tc

open Lv Restart Sec6 Exist.Staged Exist.StagedLaw

section Generic

variable {Ω 𝒴 : Type*}

/-- **A path coordinate below the rule is a mark of the rule**: if the rational time `q` lies below the rule's stop
at every sample, then `η q` is measurable for `ruleMarks 𝒢 η ζ Y S`. -/
theorem measurable_coord_ruleMarks {𝒢 : MeasurableSpace Ω} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {Y : Ω → 𝒴}
    {S : 𝒴 → (ℚ≥0 → ℂ) → ℝ≥0∞} {q : ℚ≥0} (hq : ∀ ω, ((q : ℝ≥0) : ℝ≥0∞) ≤ S (Y ω) (pathCoord (η ω))) :
    Measurable[ruleMarks 𝒢 η ζ Y S] fun ω => η ω q := by
  intro s hs
  have hF : Measurable fun k : KHist => k.1.2 q := (measurable_pi_apply q).comp (measurable_snd.comp measurable_fst)
  have e : (fun ω => η ω q) ⁻¹' s = ruleHist η ζ Y S ⁻¹' ((fun k : KHist => k.1.2 q) ⁻¹' s) := by
    ext ω
    simp only [mem_preimage, ruleHist, khistOf, histOf, stopCoord_of_le (hq ω), pathCoord]
  rw [e]
  exact le_sup_right (a := 𝒢) _ ⟨_, hF hs, rfl⟩

/-- **A path coordinate below the rule is a mark of the iterated union.** -/
theorem measurable_coord_iterMarks {𝒢 : MeasurableSpace Ω} {η : ℕ → Ω → ℝ≥0 → ℂ} {ζ : ℕ → Ω → ℝ≥0∞}
    {Y : Ω → 𝒴} {S : 𝒴 → (ℚ≥0 → ℂ) → ℝ≥0∞} (n : ℕ) {q : ℚ≥0}
    (hq : ∀ ω, ((q : ℝ≥0) : ℝ≥0∞) ≤ S (Y ω) (pathCoord (η n ω))) :
    Measurable[iterMarks 𝒢 η ζ Y S n] fun ω => η n ω q := by
  cases n with
  | zero => exact measurable_coord_ruleMarks hq
  | succ n => exact measurable_coord_ruleMarks hq

end Generic

namespace EntranceUnion

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

/-- **The capped flows are read from the absolute line marks**: `η_n` at every rational time `q ≤ T` is
`D.absMarks T`-measurable. -/
theorem measurable_ηc_absMarks (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (n : ℕ) {q : ℚ≥0} {T : ℝ≥0∞}
    (hq : ((q : ℝ≥0) : ℝ≥0∞) ≤ T) : Measurable[D.absMarks T] fun ω => D.ηc n ω q := by
  have h1 := measurable_coord_iterMarks (𝒢 := pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) (ζ := capLife ζ) (Y := D.point)
    (S := maxRule T) (η := D.ηc) n (q := q) fun ω => hq.trans (le_max_left _ _)
  exact h1.mono (le_iSup (fun m => iterMarks _ D.ηc (capLife ζ) D.point (maxRule T) m) n) le_rfl

end EntranceUnion

end InteractingSLE.Theorem14.SB.Tc
