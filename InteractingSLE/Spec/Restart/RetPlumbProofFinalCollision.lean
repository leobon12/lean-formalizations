/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofFinalGaussian
import InteractingSLE.Spec.Restart.FlowStopIdentLLTerminal

/-!
# Noncollision of geometric force images before a boundary stop

Packet PROVE-RETPLUMB. The inverse-map terminal theorem applies at every
positive time of a generating trace. An interior tip therefore excludes every
force-image collision, independently of the force weights.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open Sec7.PocketTraversal MartChar.RealFlow Supp7

/-- A positive-time tip in the upper half-plane excludes all right collisions. -/
theorem rightImg_ne_driver_of_tip_mem_H {W : ℝ≥0 → ℝ} {U : ℝ≥0∞}
    {γ : ℝ≥0 → ℂ} (hc : Continuous W) (h0 : W 0 = 0)
    (hg : IsGeneratingTrace W U γ) {t : ℝ≥0} (ht : 0 < t)
    (htU : (t : ℝ≥0∞) ≤ U) (hH : γ t ∈ QuantumZipper.H) (x : ℝ) :
    rightImg (fun s : ℝ => W s.toNNReal) x t ≠ W t := by
  let D : ℝ → ℝ := fun s => W s.toNNReal
  have hD : Continuous D := hc.comp continuous_real_toNNReal
  have hD0 : D 0 = 0 := by simpa only [D, Real.toNNReal_zero] using h0
  obtain ⟨hB, htip⟩ := FlowStopIdentLL.terminal_boundary_data hg ht htU hD hD0
    (fun s _ => by simp only [D, Real.toNNReal_coe])
  intro he
  have he' : rightImg D x t = D t := by simpa only [D, Real.toNNReal_coe] using he
  have him := (FlowStopIdentLL.real_tip_of_rightImg_eq hD hD0 t.coe_nonneg hB htip he').1
  exact (ne_of_gt (show 0 < (γ t).im from hH)) him

/-- Interior generating traces have no left or right geometric collision at
positive times. No integrated evolution is used. -/
theorem geom_images_ne_of_tip_mem_H {Ω : Type*} {W : ℝ≥0 → Ω → ℝ}
    {nL nR : ℕ} (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ)
    {V : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ} {ω : Ω}
    (hc : Continuous fun t => W t ω) (h0 : W 0 ω = 0)
    (hg : IsGeneratingTrace (fun t => W t ω) (V ω) (γ ω))
    {t : ℝ≥0} (ht : 0 < t) (htV : (t : ℝ≥0∞) ≤ V ω)
    (hH : γ ω t ∈ QuantumZipper.H) :
    (∀ i, geomLW W xL i t ω ≠ W t ω) ∧ ∀ j, geomRW W xR j t ω ≠ W t ω := by
  constructor
  · intro i he
    have href := LP.isGeneratingTrace_reflect hg
    have hHR : LP.reflectC (γ ω t) ∈ QuantumZipper.H := by
      change 0 < (LP.reflectC (γ ω t)).im
      change 0 < (γ ω t).im at hH
      simpa only [LP.reflectC, Complex.neg_im, Complex.conj_im, neg_neg] using hH
    apply rightImg_ne_driver_of_tip_mem_H hc.neg (by simp [h0]) href ht htV hHR (-xL ω i)
    change -rightImg (fun s : ℝ => -W s.toNNReal ω) (-xL ω i) t = W t ω at he
    exact neg_eq_iff_eq_neg.1 he
  · intro j
    exact rightImg_ne_driver_of_tip_mem_H hc h0 hg ht htV hH (xR ω j)

/-- Empty collision groups cannot trigger the force threshold. -/
theorem not_threshold_of_images_ne {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {w : ℝ} {vL : Fin nL → ℝ} {vR : Fin nR → ℝ}
    (hL : ∀ i, vL i ≠ w) (hR : ∀ j, vR j ≠ w) :
    ¬ ForceWord.ThresholdCondition ρL ρR w vL vR := by
  classical
  simp only [ForceWord.ThresholdCondition,
    Finset.filter_eq_empty_iff.2 (fun i _ => hL i),
    Finset.filter_eq_empty_iff.2 (fun j _ => hR j), Finset.sum_empty]
  norm_num

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The actual retained trace is interior before its boundary-stopped lifetime.
The real line in `retStopSet` is essential in this argument. -/
theorem retPath_mem_H_before_life {G : ℝ≥0 → Set Ω}
    {η₁' η₂' : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r : ℝ≥0}
    {x₂ : ℝ} {ω : Ω} (hd : (retFam G η₁' η₂' u r).IsMeasGood)
    (hG : ω ∈ G r) (hp₂ : IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : Sec7.Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r)
    {q : ℝ≥0} (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < retLife G η₁' η₂' ζ₂ u r ω) :
    retPath G η₁' η₂' ζ₂ u r ω q ∈ QuantumZipper.H := by
  obtain ⟨hC, hm, _⟩ := retChartPath_clock hd hG hp₂ hpair
  have hq' : (q : ℝ≥0∞) < capLife
      (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω))
      (retLifeP η₁' η₂' ζ₂ u r ω) := by simpa only [retLife_eq] using hq
  let s := invClock (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω))
    (retLifeP η₁' η₂' ζ₂ u r ω) q
  obtain ⟨hsle, hCs⟩ := hC.invClock_spec hq'.le
  change chartClock (retChartPath G η₁' η₂' ζ₂ u r ω) s = q at hCs
  have hs : (s : ℝ≥0∞) < retLifeP η₁' η₂' ζ₂ u r ω := by
    apply lt_of_toNNReal_lt_capLife hm
    simpa only [hCs, Real.toNNReal_coe] using hq'
  have hs0 : 0 < s := by
    have he := hC.strictMonoOn_invClock
      (show ((0 : ℝ≥0) : ℝ≥0∞) ≤ capLife _ _ from zero_le) hq'.le hq0
    simpa only [invClock_zero hC] using he
  obtain ⟨hR, hD, hL⟩ := isRetCont_retFam hd hG hp₂ hpair
  have hstop : ((r + s : ℝ≥0) : ℝ≥0∞) <
      contStop (η₂' ω) (ζ₂ ω) r (retStopSet η₁' η₂' u r ω) :=
    coe_add_lt_iff.1 hs
  have hbar := Supp7.IsPathGood.mem_Hbar_of_le hp₂ (hstop.le.trans contStop_le)
  have hreal : η₂' ω (r + s) ∉ realLine := by
    intro he
    exact notMem_of_lt_contStop (lt_add_of_pos_right r hs0) hstop (Or.inr he)
  have hH : η₂' ω (r + s) ∈ QuantumZipper.H :=
    lt_of_le_of_ne hbar (Ne.symm hreal)
  have hchart := (hR.contPath_mem_H hs0 (hL ▸ hs) hH).1
  rw [retPath, canonRetPath_zero]
  change retChartPath G η₁' η₂' ζ₂ u r ω s ∈ QuantumZipper.H
  simpa only [retChartPath, hD, hL] using hchart

end InteractingSLE.Restart.RetAux79
