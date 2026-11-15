import InteractingSLE.Spec.Sec5.Aux61RestartBdryCorridor
import InteractingSLE.Spec.Sec5.Aux61KernelTop

/-!
# The window's boundary marking on actual retained histories

Packet PROVE-AUX61-R1. Good hitting histories protect every nonzero real
point after negative inversion. The finite interior own prefix also avoids
the positive real boundary. Consequently the window's collar marking at
some positive real point is equivalent to the chart's physical marking at 1.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Aux61Restart

open WangWu LawUnique GlueCond CrossCond.Word49 CfRegQ Prop411Q

/-- Negative inversion transfers the good history's real-boundary protection
to every nonzero real point, not only to the physical mark 1. -/
theorem real_boundary_protected_of_goodHit
    {y : HistorySpace 0 0} (hy : y ∈ goodHitSet) (s : ℝ≥0)
    {x : ℝ} (hx : x ≠ 0) :
    (x : ℂ) ∉ closure (negInv '' fwdHull (cfDrv0 s y) s) := by
  intro hcl
  have hm : MapsTo negInv (negInv '' fwdHull (cfDrv0 s y) s)
      (fwdHull (cfDrv0 s y) s) := by
    rintro _ ⟨z, hz, rfl⟩
    simpa only [negInv_negInv] using hz
  have hi := (continuousAt_negInv (ofReal_ne_zero.2 hx)).continuousWithinAt.mem_closure
    hcl hm
  have hzero := eq_zero_of_mem_closure_cfDrv0 hy s _ hi
    (by simp only [negInv, neg_im, inv_im, ofReal_im, neg_zero, zero_div])
  exact (neg_ne_zero.2 (inv_ne_zero (ofReal_ne_zero.2 hx))) hzero

/-- The reflected stopped hull is closed for a good hitting history. -/
theorem isClosed_stopped_reflected_hull_of_goodHit
    {y : HistorySpace 0 0} (hy : y ∈ goodHitSet) (s : ℝ≥0) :
    IsClosed (negInv '' fwdHull (cfDrv0 s y) s) := by
  rw [fwdHull_cfDrv0 hy.1 s]
  exact (isClosed_negInv_fwdHull_of_mem_goodHitSet hy s.coe_nonneg).1

/-- The entire real-boundary protection holds at every finite retained time
on the actual glued law, by the already transferred good hitting event. -/
theorem cfGlueAE_real_boundary_protected :
    CfGlueAE.{u} fun _ y => ∀ s : ℝ≥0, ∀ x : ℝ, x ≠ 0 →
      (x : ℂ) ∉ closure (negInv '' fwdHull (cfDrv0 s y) s) := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF h44 Ω mΩ P _ 𝓕 W VL VR B ζ h hC
    Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk
  filter_upwards [cfGlueAE_mem_goodHitSet κ hκ hκ4 xL xR ρL ρR hF h44 P
    𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk] with p hp s x hx
  exact real_boundary_protected_of_goodHit hp s hx

/-- A finite interior prefix preserves the positive real boundary clearance
of the counterflow hull. The prefix's initial point is exactly 0. -/
theorem positive_boundary_free_retained_obstacle
    {K : Set ℂ} {η : ℝ → ℂ} {t : ℝ}
    (hc : ContinuousOn η (Icc 0 t)) (h0 : η 0 = 0)
    (hH : MapsTo η (Ioc 0 t) H)
    (hK : ∀ x : ℝ, 0 < x → (x : ℂ) ∉ closure K) :
    ∀ x : ℝ, 0 < x → (x : ℂ) ∉ closure (K ∪ η '' Icc 0 t) := by
  intro x hx hcl
  rw [closure_union, (isCompact_Icc.image_of_continuousOn hc).isClosed.closure_eq] at hcl
  rcases hcl with hcl | ⟨v, hv, heq⟩
  · exact hK x hx hcl
  · rcases hv.1.eq_or_lt with hv0 | hv0
    · rw [← hv0, h0] at heq
      exact (ofReal_ne_zero.2 hx.ne') heq.symm
    · have him := hH ⟨hv0, hv.2⟩
      rw [heq] at him
      exact (lt_irrefl (0 : ℝ)) (by simpa only [QuantumZipper.H,
        mem_ofPred_eq, ofReal_im] using him)

/-- The window and chart target markings agree for the source's finite
interior prefix. No junction of the counterflow chart replaces target 1. -/
theorem isTargetComp_iff_original_target
    {w : ℝ → ℝ} {s t : ℝ} {η : ℝ → ℂ} {b : ℂ}
    (hc : ContinuousOn η (Icc 0 t)) (h0 : η 0 = 0)
    (hH : MapsTo η (Ioc 0 t) H)
    (hK : ∀ x : ℝ, 0 < x → (x : ℂ) ∉ closure (Prop51G.cfHullQ w s)) :
    Aux61Kernel.IsTargetComp w s η t b ↔
      (1 : ℂ) ∈ closure (restartComponent (Prop51G.cfHullQ w s) η t b) := by
  constructor
  · exact original_target_mem_closure_of_positive_collar
      (positive_boundary_free_retained_obstacle hc h0 hH hK)
  · intro hmark
    obtain ⟨δ, hδ, hcol⟩ := exists_original_right_target_component_collar hc h0 hH
      (hK 1 zero_lt_one) hmark
    exact ⟨1, zero_lt_one, Metric.mem_nhdsWithin_iff.2
      ⟨δ, hδ, fun z hz => hcol (by simpa only [ofReal_one] using hz)⟩⟩

/-- The consumer's target condition on a good stopped history is exactly the
physical original-target marking used by the restart chart. -/
theorem isTargetComp_cfDrv0_iff_original_target
    {y : HistorySpace 0 0} (hy : y ∈ goodHitSet) (s : ℝ≥0)
    {η : ℝ → ℂ} (hη : IsProperArc η) {t : ℝ} {b : ℂ} :
    Aux61Kernel.IsTargetComp (cfDrv0 s y) s η t b ↔
      (1 : ℂ) ∈ closure
        (restartComponent (negInv '' fwdHull (cfDrv0 s y) s) η t b) :=
  isTargetComp_iff_original_target (hη.cont.mono Icc_subset_Ici_self) hη.zero
    (fun v hv => hη.mem_H v hv.1)
    (fun _ hx => real_boundary_protected_of_goodHit hy s hx.ne')

end InteractingSLE.Sec5.Aux61Restart
