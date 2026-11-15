/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC8FlowWord
import InteractingSLE.Spec.Sec7.PocketSideInSurviveLoewner

/-!
# Incident old half-discs from a surviving real trajectory

PROVE-SIDE-COLLAR2. At any two ordered own stops, a real trajectory that
survives through the later stop supplies the earlier incident half-disc,
the full transition limit, and the canonical zero inherited lift limit.
These are conclusions, not geometric hypotheses.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Sec7.PocketStopSide

/-- A surviving incoming real trajectory supplies the actual incident
old half-disc and transition limit at two ordered own times. -/
theorem exists_own_collar_of_surviving_real {c : Chart} (hc : c.IsConformal)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {s t x : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) {a : ℝ → ℂ} (ha : QuantumZipper.IsForwardSol W x t a) :
    ∃ ε : ℝ, 0 < ε ∧
      (c.loewner W s).2.1 '' (H ∩ ball ((a s).re : ℂ) ε) ⊆ ((c.loewner W t).dom : Set ℂ) ∧
      Tendsto (fun z => (c.loewner W s).1 ((c.loewner W t).2.1 z))
        (𝓝[H] ((a t).re : ℂ)) (𝓝 ((a s).re : ℂ)) ∧
      Tendsto (fun z => (c.loewner W t).2.2 ((c.loewner W t).2.1 z) -
        (c.loewner W s).2.2 ((c.loewner W t).2.1 z))
        (𝓝[H] ((a t).re : ℂ)) (𝓝 0) := by
  have ht := hs.trans hst
  have haS := QuantumZipper.isForwardSol_restrict ha hs hst
  have hInvS := tendsto_inverse_of_surviving_real hW hW0 hs haS
  have hInvT := tendsto_inverse_of_surviving_real hW hW0 ht ha
  have hNear := hInvS.eventually (ZhanGT4.eventually_not_mem_fwdHull hW ht ha)
  obtain ⟨ε, hε, hεNear⟩ := Metric.mem_nhdsWithin_iff.1 hNear
  have hCollar : (c.loewner W s).2.1 '' (H ∩ ball ((a s).re : ℂ) ε) ⊆
      ((c.loewner W t).dom : Set ℂ) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [dom_own_stage_as_initial_inverse_image hc hW hW0 ht]
    exact ⟨fwdMapInv W s z, hεNear ⟨hz.2, hz.1⟩, rfl⟩
  have hReal : a s = ((a s).re : ℂ) := Complex.ext rfl
    (by simpa using im_eq_zero_of_isForwardSol_real hW haS ⟨hs, le_rfl⟩)
  have hForward := (tendsto_fwdMap_of_isForwardSol hW hs haS).comp hInvT
  rw [hReal] at hForward
  have hTransition : Tendsto (fun z => (c.loewner W s).1 ((c.loewner W t).2.1 z))
      (𝓝[H] ((a t).re : ℂ)) (𝓝 ((a s).re : ℂ)) := by
    refine hForward.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
    change fwdMap W s (fwdMapInv W t z) = fwdMap W s (c.1 (c.2.1 (fwdMapInv W t z)))
    rw [hc.2.2 _ (QuantumZipper.RS.fwdMapInv_mem_H hW hW0 ht hz)]
  exact ⟨ε, hε, hCollar, hTransition,
    tendsto_own_stage_lift_sub_zero hc hW hW0 hs hst hε hCollar hTransition⟩

end InteractingSLE.Sec7.PocketStopSide
