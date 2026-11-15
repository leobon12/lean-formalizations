/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2FinalCollision

/-!
# Incident heights at untouched real points of the first-contact chart
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)

namespace InteractingSLE.Restart.FCPlumb
open PiecewiseConstantBoundaryData
variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω}

/-- At a real chart point outside the filled base whose original preimage is
off the jump candidates, both incident heights read the original datum. -/
theorem word_limits_of_untouched (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    {c₀ : BoundaryWord} (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1))
    (hb₀ : ∀ y ∉ J, c₀.fn y = b y) (hL hR : ℝ) {w : ℝ}
    (hw : w < d.wordL ω ∨ d.wordR ω < w) (hyJ : (d.inv ω w).re ∉ J) :
    leftLim (d.word c₀ hL hR ω).fn w = b (d.inv ω w).re ∧
      rightLim (d.word c₀ hL hR ω).fn w = b (d.inv ω w).re := by
  obtain ⟨-, -, -, -, -, -, -, hψc, -⟩ := (hd.isFirstContactChart hE).2
  have hm : Continuous fun r : ℝ => (d.inv ω (r : ℂ)).re :=
    Complex.continuous_re.comp (hψc.comp_continuous Complex.continuous_ofReal
      (fun r => by simp only [Hbar, Complex.ofReal_im, Set.mem_ofPred_eq, le_refl]))
  have hj : {y : ℝ | y ∉ J} ∈ 𝓝 (d.inv ω w).re :=
    J.finite_toSet.isClosed.isOpen_compl.mem_nhds hyJ
  have he := (hm.tendsto w).eventually ((hb _ hyJ).and hj)
  have ht : ∀ᶠ r in 𝓝 w, (d.word c₀ hL hR ω).fn r = b (d.inv ω w).re := by
    rcases hw with hw | hw
    · filter_upwards [he, Iio_mem_nhds hw] with r hr hrL
      rw [hd.word_fn_of_lt_wordL hE hc₀ hL hR hrL, hb₀ _ hr.2]
      exact hr.1
    · filter_upwards [he, Ioi_mem_nhds hw] with r hr hRr
      rw [hd.word_fn_of_wordR_lt hE hc₀ hL hR hRr, hb₀ _ hr.2]
      exact hr.1
  exact ⟨(tendsto_const_nhds.congr' (ht.mono fun r hr => hr.symm)).mono_left nhdsWithin_le_nhds |>.limUnder_eq,
    (tendsto_const_nhds.congr' (ht.mono fun r hr => hr.symm)).mono_left nhdsWithin_le_nhds |>.limUnder_eq⟩

/-- A positive fresh line tip on the real chart boundary lies outside the
old filled-base interval. -/
theorem real_tip_outside_word_interval (hd : d.IsMeasGood)
    {ω : Ω} {x₁ x₂ : ℝ} {t Q : ℝ≥0} {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {U : ℝ≥0∞}
    (hl : FCAux79.IsFCLine d ω x₁ x₂ t W γ U Q) (him : (γ Q).im = 0) :
    (γ Q).re < d.wordL ω ∨ d.wordR ω < (γ Q).re := by
  by_contra hn
  push Not at hn
  have hK := hd.inv_mem_K_of_mem_Icc hl.mem_E hn.1 hn.2
  rw [Sec7.SideHeightBox.ofReal_re_of_im him, hl.tip] at hK
  exact hl.notMem_K hd (lt_add_of_pos_right _ (hl.t_pos hd)) le_rfl hK

/-- A live source visit to an untouched chart point gives the incident
inequality there for the same angle. The visit event is simultaneous in time. -/
theorem word_incident_bounds_of_live_visit (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E)
    {κ θ x : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    {c₀ : BoundaryWord} (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1))
    (hb₀ : ∀ y ∉ J, c₀.fn y = b y) (hL hR : ℝ)
    {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} (hzero : η 0 = x)
    (hxL : d.baseL ω ≤ x) (hxR : x ≤ d.baseR ω)
    (hv : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ y : ℝ, η t = y →
      (y ≤ x → leftLim b y + θ * chiC κ < sleLambda κ) ∧
      (x ≤ y → -sleLambda κ < rightLim b y + θ * chiC κ))
    (hj : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ → ∀ y ∈ J, y ≠ x → η t ≠ y)
    {w : ℝ} (hw : w < d.wordL ω ∨ d.wordR ω < w)
    (hvisit : ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ∧ η t = d.inv ω w) :
    (w ≤ 0 → leftLim (d.word c₀ hL hR ω).fn w + θ * chiC κ < sleLambda κ) ∧
    (0 ≤ w → -sleLambda κ < rightLim (d.word c₀ hL hR ω).fn w + θ * chiC κ) := by
  obtain ⟨t, ht, he⟩ := hvisit
  set y : ℝ := (d.inv ω w).re
  have ho := hw
  rcases hw with hw | hw
  · obtain ⟨hya, hy, -⟩ := hd.inv_of_lt_wordL hE hw
    have hyx : y < x := hya.trans_le hxL
    have het : η t = (y : ℂ) := he.trans hy
    have ht0 : 0 < t := pos_iff_ne_zero.2 fun ht0 => by
      rw [ht0, hzero] at het
      exact hyx.ne' (Complex.ofReal_injective het)
    have hyJ : y ∉ J := fun hyJ => hj t ht0 ht y hyJ hyx.ne het
    have hl := (word_limits_of_untouched hd hE hb hc₀ hb₀ hL hR ho hyJ).1
    rw [hl, ← Exist.StagedLaw.leftLim_eq_of_notMem hb hyJ]
    exact ⟨fun _ => (hv t ht y het).1 hyx.le,
      fun h => False.elim ((not_lt_of_ge h) (hw.trans_le (hd.wordL_nonpos hE)))⟩
  · obtain ⟨hby, hy, -⟩ := hd.inv_of_wordR_lt hE hw
    have hxy : x < y := hxR.trans_lt hby
    have het : η t = (y : ℂ) := he.trans hy
    have ht0 : 0 < t := pos_iff_ne_zero.2 fun ht0 => by
      rw [ht0, hzero] at het
      exact hxy.ne (Complex.ofReal_injective het)
    have hyJ : y ∉ J := fun hyJ => hj t ht0 ht y hyJ hxy.ne' het
    have hr := (word_limits_of_untouched hd hE hb hc₀ hb₀ hL hR ho hyJ).2
    rw [hr, ← Exist.StagedLaw.rightLim_eq_of_notMem hb hyJ]
    exact ⟨fun h => False.elim ((not_lt_of_ge h) ((hd.wordR_nonneg hE).trans_lt hw)),
      fun _ => (hv t ht y het).2 hxy.le⟩

end InteractingSLE.Restart.FCPlumb
