/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Prob41Avoid
import InteractingSLE.Spec.Sec7.LocalExtA2Mart
import InteractingSLE.Spec.Sec7.ContinuityProb2Restart
import InteractingSLE.Spec.Zhan.TargetChangeProcessPullEnd

/-!
# Aux. lemma 22 in the strip, step 3a: a generating trace avoids alive real points, on a finite horizon

Packet PROVE-SEC5-L (specification §4.1, Aux. lemma 22, pp. 113–115: "Taking the countable intersection of the
corresponding noncollision events, a continuous first contact with such an arc would swallow one of these passive
marks … contrary to noncollision. Thus these arcs cannot be hit before the asserted endpoint").

PROVE-SEC4-A3's `Sec4.ne_ofReal_of_isGeneratingTrace` (a generating trace never visits a closed real set of alive
points) is stated for a trace on `[0, ∞)` and a globally continuous driver. The strip evolutions of Aux. lemma 22 are
only known up to the end of their strip life, so this file proves the finite-horizon form:

* `ne_ofReal_of_isGeneratingTrace_le`: the same argument for a trace on `[0, T]` and points alive on `[0, t₁]`,
  `t₁ < T` (globally continuous driver);
* **`ne_ofReal_of_isGeneratingTrace_lt`**: the same for a driver that is only continuous before `T` (the driver is
  frozen after a time between `t₁` and `T`; hulls and forward solutions only see the driver up to their time).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal

open QuantumZipper (H IsForwardSol fwdMap fwdHull)

namespace InteractingSLE

namespace Sec5

namespace Aux22Strip

open Sec4

/-- **A generating trace never visits a closed real set of points alive up to `t₁`** (before `t₁`, finite horizon,
globally continuous driver). The proof of `Sec4.ne_ofReal_of_isGeneratingTrace`, with the hull identity used only at
times `≤ t₁ < T`. -/
theorem ne_ofReal_of_isGeneratingTrace_le {w : ℝ≥0 → ℝ}
    (hW : Continuous fun s : ℝ => w s.toNNReal) (hw0 : w 0 = 0) {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w T η) {C : Set ℝ} (hC : IsClosed C) (h0 : (0 : ℝ) ∉ C) {t₁ : ℝ≥0}
    (ht₁ : (t₁ : ℝ≥0∞) < T)
    (halive : ∀ y ∈ C, ∃ v, IsForwardSol (fun s : ℝ => w s.toNNReal) (y : ℂ) t₁ v) :
    ∀ t : ℝ≥0, t ≤ t₁ → ∀ y ∈ C, η t ≠ y := by
  set W : ℝ → ℝ := fun s => w s.toNNReal with hWdef
  have hW0 : W 0 = 0 := by simp [hWdef, hw0]
  obtain ⟨hη0, hηc, hfill⟩ := hη
  have hlt : ∀ s : ℝ≥0, s ≤ t₁ → (s : ℝ≥0∞) < T := fun s hs =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) ht₁
  have hηI : ContinuousOn η (Iic t₁) := hηc.mono fun s hs => (hlt s hs).le
  have hηat : ∀ s : ℝ≥0, s ≤ t₁ → ContinuousAt η s := fun s hs => by
    have hopen : IsOpen {r : ℝ≥0 | (r : ℝ≥0∞) < T} := isOpen_lt ENNReal.continuous_coe continuous_const
    exact hηc.continuousAt (Filter.mem_of_superset (hopen.mem_nhds (hlt s hs))
      fun r hr => show (r : ℝ≥0∞) ≤ T from le_of_lt hr)
  intro t₀ ht₀ y₀ hy₀ hηt₀
  set S : Set ℝ≥0 := Iic t₁ ∩ η ⁻¹' (((↑) : ℝ → ℂ) '' C) with hSdef
  have hCc : IsClosed (((↑) : ℝ → ℂ) '' C) :=
    Complex.isometry_ofReal.isClosedEmbedding.isClosedMap _ hC
  have hSc : IsClosed S := hηI.preimage_isClosed_of_isClosed isClosed_Iic hCc
  have hSne : S.Nonempty := ⟨t₀, ht₀, y₀, hy₀, hηt₀.symm⟩
  set s₀ : ℝ≥0 := sInf S with hs₀def
  have hs₀S : s₀ ∈ S := hSc.csInf_mem hSne (OrderBot.bddBelow S)
  have hs₀t : s₀ ≤ t₁ := hs₀S.1
  replace hs₀S := hs₀S.2
  obtain ⟨y, hyC, hy⟩ := hs₀S
  have hs₀pos : 0 < s₀ := by
    rcases eq_zero_or_pos s₀ with h | h
    · exfalso
      rw [h, hη0] at hy
      have hy' : y = 0 := by exact_mod_cast hy
      exact h0 (hy' ▸ hyC)
    · exact h
  obtain ⟨v, hv⟩ := halive y hyC
  replace hv := QuantumZipper.isForwardSol_restrict hv s₀.coe_nonneg (NNReal.coe_le_coe.2 hs₀t)
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol s₀.coe_nonneg hv
  set E : ℝ := Real.exp (2 / δ ^ 2 * s₀) with hEdef
  have hE : 0 < E := Real.exp_pos _
  have hnot : ∀ z : ℂ, 0 < z.im → ‖z - y‖ < δ / E → z ∉ fwdHull W s₀ := fun z hz hzy =>
    not_mem_fwdHull_of_isForwardSol hW hv hδ hlow hz (by rwa [lt_div_iff₀ hE] at hzy)
  obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.1 (hηat s₀ hs₀t) (δ / E) (div_pos hδ hE)
  have hcompact : ∀ s : ℝ≥0, s ≤ t₁ → IsCompact (η '' Icc 0 s) := fun s hs =>
    isCompact_Icc.image_of_continuousOn (hηI.mono fun r hr => hr.2.trans hs)
  have hK : ∀ s : ℝ≥0, s ≤ t₁ → fwdHull W s = fillH (η '' Icc 0 s) := fun s hs => by
    have h := hfill s (hlt s hs)
    rw [isFilling_iff_inter_H_eq_fillH (hcompact s hs).isBounded (hcompact s hs).isClosed,
      inter_eq_left.2 ((QuantumZipper.fwdHull_mono (W := W)).2 _)] at h
    exact h
  -- trace points just before `s₀` are not in `ℍ`
  have hnotH : ∀ s : ℝ≥0, s < s₀ → dist s s₀ < ε → ¬ 0 < (η s).im := by
    intro s hs hd hpos
    have hmem : η s ∈ fwdHull W s₀ := by
      rw [hK s₀ hs₀t]
      exact ⟨hpos, Or.inl (subset_closure ⟨s, ⟨zero_le, hs.le⟩, rfl⟩)⟩
    refine hnot (η s) hpos ?_ hmem
    have := hball hd
    rwa [dist_eq_norm, ← hy] at this
  set s₁ : ℝ≥0 := Real.toNNReal ((s₀ : ℝ) - ε / 2) with hs₁def
  have hs₁' : (s₁ : ℝ) = max ((s₀ : ℝ) - ε / 2) 0 := Real.coe_toNNReal' _
  have hs₁ : s₁ < s₀ := by
    rw [← NNReal.coe_lt_coe, hs₁']
    exact max_lt (by linarith) (NNReal.coe_pos.2 hs₀pos)
  have hdist : ∀ s : ℝ≥0, s₁ < s → s < s₀ → dist s s₀ < ε := by
    intro s h1 h2
    rw [NNReal.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.2 (NNReal.coe_lt_coe.2 h2))]
    have h1' : (s₁ : ℝ) < s := NNReal.coe_lt_coe.2 h1
    have : (s₀ : ℝ) - ε / 2 ≤ s₁ := by rw [hs₁']; exact le_max_left _ _
    linarith
  have hAH : η '' Icc 0 s₀ ∩ H = η '' Icc 0 s₁ ∩ H := by
    ext z
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, hz⟩
      refine ⟨⟨s, ⟨hs.1, ?_⟩, rfl⟩, hz⟩
      by_contra hlt
      have hlt' : s₁ < s := lt_of_not_ge hlt
      rcases hs.2.lt_or_eq with h | h
      · exact hnotH s h (hdist s hlt' h) hz
      · have hz' : (0 : ℝ) < (η s).im := hz
        rw [h, ← hy, Complex.ofReal_im] at hz'
        exact lt_irrefl _ hz'
    · rintro ⟨⟨s, hs, rfl⟩, hz⟩
      exact ⟨⟨s, ⟨hs.1, hs.2.trans hs₁.le⟩, rfl⟩, hz⟩
  have heq : fwdHull W s₀ = fwdHull W s₁ := by
    rw [hK s₀ hs₀t, hK s₁ (hs₁.le.trans hs₀t)]
    exact Sec4.fillH_congr (hcompact _ hs₀t).isClosed (hcompact _ (hs₁.le.trans hs₀t)).isClosed hAH
  have hss := QuantumZipper.RS.fwdHull_ssubset hW hW0 s₁.coe_nonneg (NNReal.coe_lt_coe.2 hs₁)
  rw [heq] at hss
  exact hss.ne rfl


/-- The path `w` frozen after time `t₂`. -/
def freezeAt (w : ℝ≥0 → ℝ) (t₂ : ℝ≥0) : ℝ≥0 → ℝ := fun s => w (min s t₂)

theorem freezeAt_of_le {w : ℝ≥0 → ℝ} {t₂ s : ℝ≥0} (hs : s ≤ t₂) : freezeAt w t₂ s = w s := by
  simp [freezeAt, min_eq_left hs]

/-- A path continuous on `[0, t₂]` is continuous after freezing at `t₂` (read on `ℝ`). -/
theorem continuous_freezeAt {w : ℝ≥0 → ℝ} {t₂ : ℝ≥0} (hw : ContinuousOn w (Iic t₂)) :
    Continuous fun s : ℝ => freezeAt w t₂ s.toNNReal := by
  have hm : Continuous fun s : ℝ => min s.toNNReal t₂ := continuous_real_toNNReal.min continuous_const
  exact hw.comp_continuous hm fun s => mem_Iic.2 (min_le_right _ _)

/-- **A generating trace never visits a closed real set of points alive up to `t₁`**, for a driver continuous
before the horizon `T > t₁` (freeze the driver at a time between `t₁` and `T`). -/
theorem ne_ofReal_of_isGeneratingTrace_lt {w : ℝ≥0 → ℝ} {T : ℝ≥0∞}
    (hW : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w T η) {C : Set ℝ} (hC : IsClosed C) (h0 : (0 : ℝ) ∉ C) {t₁ : ℝ≥0}
    (ht₁ : (t₁ : ℝ≥0∞) < T)
    (halive : ∀ y ∈ C, ∃ v, IsForwardSol (fun s : ℝ => w s.toNNReal) (y : ℂ) t₁ v) :
    ∀ t : ℝ≥0, t ≤ t₁ → ∀ y ∈ C, η t ≠ y := by
  obtain ⟨t₂, h12, h2T⟩ : ∃ t₂ : ℝ≥0, t₁ < t₂ ∧ (t₂ : ℝ≥0∞) < T := by
    obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht₁
    exact ⟨r, ENNReal.coe_lt_coe.1 hr1, hr2⟩
  have hW2 : ContinuousOn w (Iic t₂) := hW.mono fun s hs =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) h2T
  have hη' : IsGeneratingTrace (freezeAt w t₂) t₂ η :=
    Sec7.IsGeneratingTrace.congr_lt (hη.mono_horizon h2T.le) fun t ht =>
      freezeAt_of_le (ENNReal.coe_le_coe.1 ht.le)
  refine ne_ofReal_of_isGeneratingTrace_le (continuous_freezeAt hW2) (by rw [freezeAt_of_le zero_le, hw0])
    hη' hC h0 (ENNReal.coe_lt_coe.2 h12) fun y hy => ?_
  obtain ⟨v, hv⟩ := halive y hy
  refine ⟨v, LocalExt.isForwardSol_congr (fun s hs => ?_) hv⟩
  have hs' : s.toNNReal ≤ t₂ := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]
    exact hs.2.trans (NNReal.coe_le_coe.2 h12.le)
  exact (freezeAt_of_le hs').symm

/-- **A bounded generating trace has bounded capacity time** (the capacity argument of
`Zhan.Retarget.PullData.not_bounded_top`): if `‖η‖ ≤ B` on `[0, t]`, `t < T`, then `2t ≤ B²`. -/
theorem two_mul_le_sq_of_isGeneratingTrace {w : ℝ≥0 → ℝ} {T : ℝ≥0∞}
    (hW : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w T η) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) {B : ℝ}
    (hB : ∀ s : ℝ≥0, s ≤ t → ‖η s‖ ≤ B) : 2 * (t : ℝ) ≤ B ^ 2 := by
  obtain ⟨t₂, h12, h2T⟩ : ∃ t₂ : ℝ≥0, t < t₂ ∧ (t₂ : ℝ≥0∞) < T := by
    obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
    exact ⟨r, ENNReal.coe_lt_coe.1 hr1, hr2⟩
  have hW2 : ContinuousOn w (Iic t₂) := hW.mono fun s hs =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) h2T
  set W' : ℝ → ℝ := fun s => freezeAt w t₂ s.toNNReal with hW'def
  have hW'c : Continuous W' := continuous_freezeAt hW2
  have hW'0 : W' 0 = 0 := by
    simp only [hW'def, Real.toNNReal_zero]
    rw [freezeAt_of_le zero_le, hw0]
  set A := η '' Icc 0 t with hA
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn
    (hη.2.1.mono fun s hs => (ENNReal.coe_le_coe.2 hs.2).trans ht.le)
  have hfill := hη.2.2 t ht
  have hKeq := (fillH_eq_iff_isFilling_of_isClosed hAc.isBounded hAc.isClosed
    ((QuantumZipper.fwdHull_mono).2 _)).1 hfill
  have hAB : closure A ⊆ Metric.closedBall 0 B := by
    rw [hAc.isClosed.closure_eq]
    rintro _ ⟨s, hs, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hB s hs.2
  have hKB : fwdHull (fun s : ℝ => w s.toNNReal) t ⊆ Metric.closedBall 0 B :=
    hKeq ▸ fillH_subset_closedBall_zero hAB
  have hK' : fwdHull (fun s : ℝ => w s.toNNReal) t = fwdHull W' t := by
    refine fwdHull_eq_of_eqOn t.coe_nonneg (NNReal.coe_lt_coe.2 h12) fun r hr => ?_
    have hr' : r.toNNReal ≤ t₂ := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]
      exact hr.2
    exact (freezeAt_of_le hr').symm
  have hcap := hcap_fwdHull hW'c hW'0 t.coe_nonneg
  have hKB' : fwdHull W' t ⊆ Metric.closedBall ((0 : ℝ) : ℂ) B := by rw [← hK']; simpa using hKB
  have hle := HPHull.hcap_le_rad_sq ⟨fwdHull W' t, InteractingSLE.isHPHull_fwdHull hW'c t.coe_nonneg⟩
    (x := 0) (r := B) hKB'
  rw [hcap] at hle
  exact hle

end Aux22Strip

end Sec5

end InteractingSLE
