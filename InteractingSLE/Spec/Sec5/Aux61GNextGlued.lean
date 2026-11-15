/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GNextLanding
import InteractingSLE.Spec.Sec5.Aux61GInstGluedLanding

/-! # Finite real landing for the actual retained first contact -/

set_option autoImplicit false
noncomputable section
open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)

namespace InteractingSLE.Sec5.Aux61GNext
open Aux61FibData Aux61Restart Aux61GInst
open WangWu (negInv)

/-- The actual retained traces give the inverse extension; the actual
first-hit rule gives boundary contact. Original-target normalization then
gives a finite real coordinate for every finite non-target endpoint. -/
theorem exists_real_glued_accessEndpoint {X : Type*} [MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}
    (hs : IsRestartSpec E c ρ T) {x : X} (hx : x ∈ E)
    (hpos : 0 < T x) (hfin : T x < ⊤)
    {W : ℝ → ℝ} {β η : ℝ → ℂ} {s r : ℝ} (hs0 : 0 ≤ s)
    (hβ : IsLoewnerTrace W β) (hη : ContinuousOn η (Icc 0 r))
    (hηH : MapsTo η (Icc 0 r) Hbar) {b : ℂ}
    (hb : b ∈ retainedDomain (negInv '' QuantumZipper.fwdHull W s) η r)
    (hdom : ((c x).dom : Set ℂ) = restartComponent (negInv '' QuantumZipper.fwdHull W s) η r b)
    (hDs : IsSimplyConnected ((c x).dom : Set ℂ))
    (htarget : ∃ δ > 0, ball (1 : ℂ) δ ∩ H ⊆ (c x).dom)
    (hscale : ∃ a ξ : ℝ, 0 < a ∧ EqOn (c x).1 (fun z => (a : ℂ) *
      (ConformalImage.mapOut (stripTargetHull ((c x).dom : Set ℂ)) (stripRightRetarget z) - ξ)) (c x).dom)
    (hfirst_contact : T x = hitTime ρ (fun _ => (H \ negInv '' QuantumZipper.fwdHull W s)ᶜ) x)
    (hnot_target : ρ x (T x).toNNReal ≠ 1) :
    ∃ y : ℝ, y ≠ 0 ∧ boundedInverse (c x) (y : ℂ) = cayley (ρ x (T x).toNNReal) ∧
      Tendsto (inPath E c ρ T x) (𝓝[<] (T x).toNNReal) (𝓝 (y : ℂ)) := by
  have hc := hs.conf x hx
  have hF := boundedInverse_spec_of_traces hβ hs0 hη hηH hb hc hdom
  have hK : IsCompact (counterflowRecord β s) := isCompact_Icc.image_of_continuousOn
    (continuous_clipH.comp_continuousOn (hβ.2.1.mono Icc_subset_Ici_self))
  have hopen : IsOpen (H \ negInv '' QuantumZipper.fwdHull W s) := by
    rw [← fillH_clipped_trace hβ hs0, WangWu.H_diff_image_negInv]
    exact WangWu.isOpen_image_negInv (isOpen_H_diff_fillH hK.isBounded) sdiff_subset
  have hhit := mem_at_finite_hitTime (hs.contρ x hx) hopen.isClosed_compl hfirst_contact hfin
  have hcontact : ρ x (T x).toNNReal ∉ (c x).dom := by
    intro hm
    have hm' : ρ x (T x).toNNReal ∈ restartComponent (negInv '' QuantumZipper.fwdHull W s) η r b :=
      hdom ▸ hm
    have hret := connectedComponentIn_subset _ _ hm'
    exact hhit ⟨hret.1, fun hcf => hret.2 (Or.inl hcf)⟩
  obtain ⟨a, ξ, ha, hsc⟩ := hscale
  obtain ⟨y, hy, hylim⟩ := exists_real_accessEndpoint_of_scale hs hx hpos hfin
    (isHPHull_stripTargetHull (c x).dom.isOpen hDs hc.dom_subset htarget)
    ha hsc hF.2 hcontact hnot_target
  refine ⟨y, ?_, hy, hylim⟩
  intro hy0
  have hstart : ρ x 0 ∈ H \ negInv '' QuantumZipper.fwdHull W s := by
    have hn := notMem_of_lt_hitTime (ρ := ρ)
      (F := fun _ => (H \ negInv '' QuantumZipper.fwdHull W s)ᶜ)
      (x := x) (u := 0) (by simpa only [← hfirst_contact, ENNReal.coe_zero] using hpos)
    exact not_not.1 hn
  have hF0 := boundedInverse_zero_of_restartSpec hs hx hpos hF.1 hF.2.1
  rw [hy0, ofReal_zero, hF0] at hy
  have hxev : x ∈ exitEv E c ρ T univ := mem_exitEv_of_finite hx hpos hfin
  have hendbar : ρ x (T x).toNNReal ∈ Hbar := closure_H ▸
    closure_mono hc.dom_subset (hs.mem_closure_at_T hxev hfin)
  have he := QuantumZipper.CA.bijOn_cayley_Hbar.injOn (H_subset_Hbar hstart.1) hendbar hy
  exact hhit (he ▸ hstart)

end InteractingSLE.Sec5.Aux61GNext
