/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWordWindows
import InteractingSLE.Spec.Sec5.Aux61GNextCompleted

/-! # Pointwise capture by the fixed countable buffered windows

Complete the actual access at its finite nonzero real limit, then use the
countable family selected independently of the sample. This proves the
window geometry of capture; retained-record localization remains separate.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWord
open Aux61FibData (IsRestartSpec inPath)
open Aux61Restart Aux61GInst
open WangWu (negInv)

/-- Any finite nonzero real access endpoint is captured by one member of
the fixed countable family, with exit time equal to the physical lifetime. -/
theorem exists_countable_capture_of_access_limit {X : Type*} [MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}
    (hs : IsRestartSpec E c ρ T) {x : X} (hx : x ∈ E)
    (hpos : 0 < T x) (hfin : T x < ⊤) {y : ℝ} (hy : y ≠ 0)
    (hend : Tendsto (inPath E c ρ T x) (𝓝[<] (T x).toNNReal) (𝓝 (y : ℂ)))
    {O : Set ℝ} (hO : IsOpen O) (hO0 : 0 ∈ O) (hOy : y ∈ O) :
    ∃ i : SeedWindowIndex, 0 < ((i : WindowIndex).2.2 : ℝ) ∧ IsOpen (bufferedWindow i) ∧
      (0 : ℂ) ∈ bufferedWindow i ∧ bufferedWindow i ⊆ outerBuffer i ∧
      IsCompact (closure (outerBuffer i)) ∧
      (∀ z ∈ closure (outerBuffer i), z.im = 0 → z.re ∈ O) ∧
      (∀ r : ℝ≥0, (r : ℝ≥0∞) < T x → inPath E c ρ T x r ∈ bufferedWindow i) ∧
      (y : ℂ) ∉ bufferedWindow i ∧
      Aux61FibData.exitTime E c ρ T (bufferedWindow i) x = T x := by
  obtain ⟨γ, hγc, hγeq, hγ0, hγend, hγH⟩ :=
    Aux61GNext.exists_continuous_access_completion hs hx hpos hfin hend
  obtain ⟨i, hgap, hVo, hV0, -, hVU, -, hUc, hUr, hbefore, hyV⟩ :=
    exists_bufferedWindow_of_completed_segment hγc hγ0 hγH hγend hy hO hO0 hOy
  have hin : ∀ r : ℝ≥0, (r : ℝ≥0∞) < T x →
      inPath E c ρ T x r ∈ bufferedWindow i := by
    intro r hr
    have hrt : r < (T x).toNNReal := by
      rw [← ENNReal.coe_toNNReal hfin.ne] at hr
      exact ENNReal.coe_lt_coe.1 hr
    rw [← hγeq hrt]
    exact hbefore r hrt
  exact ⟨i, hgap, hVo, hV0, hVU, hUc, hUr, hin, hyV,
    Aux61GCont.exitTime_eq_of_before_mem hs hVo hx hin⟩

/-- For an actual finite non-target glued first contact, the retained
geometry supplies the nonzero real limit, followed by countable window
capture on every pair of permitted seed/endpoint boundary neighborhoods. -/
theorem exists_countable_capture_of_glued_contact {X : Type*} [MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}
    (hs : IsRestartSpec E c ρ T) {x : X} (hx : x ∈ E)
    (hpos : 0 < T x) (hfin : T x < ⊤)
    {W : ℝ → ℝ} {β η : ℝ → ℂ} {s r : ℝ} (hs0 : 0 ≤ s)
    (hβ : IsLoewnerTrace W β) (hη : ContinuousOn η (Icc 0 r))
    (hηH : MapsTo η (Icc 0 r) Hbar) {b : ℂ}
    (hb : b ∈ retainedDomain (negInv '' QuantumZipper.fwdHull W s) η r)
    (hdom : ((c x).dom : Set ℂ) =
      restartComponent (negInv '' QuantumZipper.fwdHull W s) η r b)
    (hDs : IsSimplyConnected ((c x).dom : Set ℂ))
    (htarget : ∃ δ > 0, Metric.ball (1 : ℂ) δ ∩ H ⊆ (c x).dom)
    (hscale : ∃ a ξ : ℝ, 0 < a ∧ EqOn (c x).1 (fun z => (a : ℂ) *
      (ConformalImage.mapOut (stripTargetHull ((c x).dom : Set ℂ))
        (stripRightRetarget z) - ξ)) (c x).dom)
    (hfirst_contact : T x =
      Aux61FibData.hitTime ρ (fun _ => (H \ negInv '' QuantumZipper.fwdHull W s)ᶜ) x)
    (hnot_target : ρ x (T x).toNNReal ≠ 1) :
    ∃ y : ℝ, y ≠ 0 ∧
      Tendsto (inPath E c ρ T x) (𝓝[<] (T x).toNNReal) (𝓝 (y : ℂ)) ∧
      ∀ O : Set ℝ, IsOpen O → 0 ∈ O → y ∈ O →
        ∃ i : SeedWindowIndex, 0 < ((i : WindowIndex).2.2 : ℝ) ∧ IsOpen (bufferedWindow i) ∧
          (0 : ℂ) ∈ bufferedWindow i ∧ bufferedWindow i ⊆ outerBuffer i ∧
          IsCompact (closure (outerBuffer i)) ∧
          (∀ z ∈ closure (outerBuffer i), z.im = 0 → z.re ∈ O) ∧
          (∀ u : ℝ≥0, (u : ℝ≥0∞) < T x →
            inPath E c ρ T x u ∈ bufferedWindow i) ∧
          (y : ℂ) ∉ bufferedWindow i ∧
          Aux61FibData.exitTime E c ρ T (bufferedWindow i) x = T x := by
  obtain ⟨y, hy, -, hlim⟩ := Aux61GNext.exists_real_glued_accessEndpoint hs hx hpos hfin
    hs0 hβ hη hηH hb hdom hDs htarget hscale hfirst_contact hnot_target
  exact ⟨y, hy, hlim, fun O hO hO0 hOy =>
    exists_countable_capture_of_access_limit hs hx hpos hfin hy hlim hO hO0 hOy⟩

end InteractingSLE.Sec5.Aux61GWord
