/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1RestartFinalRun

/-!
# The finite-contact endpoint argument in arbitrary retained charts

Distinct physical targets force a finite original contact time. This statement
does not confuse the original contact time with the infinite relative lifetime.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW1RestartFinal

/-- A retained clock cannot exhaust infinite original time when its two physical
curves have distinct terminal limits. It is the full retained set that occurs in
the first-tip time. -/
theorem firstTipTime_ne_top_of_distinct_endpoints
    {source target : Chart} {W V : ℝ≥0 → ℝ} {A : Set ℂ} {b : ℝ≥0 → ℝ≥0}
    (hclock : GW1RestartPair.IsRetainedClock source target W V A b)
    {X : Type*} [TopologicalSpace X] [T2Space X] {α γ : ℝ≥0 → X} {x y : X}
    (hα : Tendsto α atTop (𝓝 x)) (hγ : Tendsto γ atTop (𝓝 y)) (hne : x ≠ y)
    (hread : ∀ r, α (b r) = γ r) : firstTipTime source W A ≠ ⊤ := by
  intro htop
  have hsur : Function.Surjective b := by
    apply range_eq_univ.1
    rw [hclock.2.2.1, htop]
    ext s
    simp only [mem_ofPred_eq, ENNReal.coe_lt_top, mem_univ]
  have hb : Tendsto b atTop atTop := hclock.2.1.monotone.tendsto_atTop_atTop
    (fun s => by obtain ⟨r, hr⟩ := hsur s; exact ⟨r, hr.ge⟩)
  exact hne (tendsto_nhds_unique ((hα.comp hb).congr' (Eventually.of_forall hread)) hγ)

/-- Once the actual physical tip hit-times form a closed set, a finite first
tip contact is attained. This reuses the existing first-contact theorem. -/
theorem exists_attained_firstTipTime {c : Chart} {W : ℝ≥0 → ℝ} {A : Set ℂ}
    (hclosed : IsClosed {t : ℝ≥0 | ∃ z ∈ A, c.tipAt W t z})
    (hfin : firstTipTime c W A ≠ ⊤) :
    ∃ T : ℝ≥0, firstTipTime c W A = T ∧ ∃ z ∈ A, c.tipAt W T z := by
  refine ⟨(firstTipTime c W A).toNNReal, (ENNReal.coe_toNNReal hfin).symm, ?_⟩
  exact Supp8.GB6.firstContactTime_mem continuous_id hclosed
    (show Supp8.GB6.firstContactTime (id : ℝ≥0 → ℝ≥0)
      {t : ℝ≥0 | ∃ z ∈ A, c.tipAt W t z} = ((firstTipTime c W A).toNNReal : ℝ≥0∞)
      from (ENNReal.coe_toNNReal hfin).symm)

end InteractingSLE.Theorem14.GW1RestartFinal
