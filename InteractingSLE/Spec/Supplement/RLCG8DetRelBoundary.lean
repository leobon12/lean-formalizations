/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetRelImage
import InteractingSLE.Spec.ZhanGT4.D9Clear

/-!
# G8: retained boundary points are real characteristics

Packet PROVE-G8-DET. A real point off the closed relative hull survives by the
landed real-flow criterion. Its boundary value solves the characteristic
equation. Canonical retained charts are obtained by subtracting the retained
tip's boundary value from the hydrodynamic map.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMap IsForwardSol)

namespace InteractingSLE.RLC.G8Det

/-- Closure avoidance is enough to apply the existing real-flow criterion. -/
theorem alive_of_notMem_closure {W : ℝ → ℝ} (hW : Continuous W) {y s : ℝ}
    (hy : y ≠ W 0) (hs : 0 ≤ s) (hoff : (y : ℂ) ∉ closure (fwdHull W s)) :
    ∃ v, IsForwardSol W (y : ℂ) s v := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ hoff
  exact ZhanGT4.exists_isForwardSol_of_disjoint_ball_gen hW hy hs hδ
    (Set.disjoint_left.2 fun z hz hzK => hsub hz (subset_closure hzK))

/-- The retained point left of the seed is a strict left characteristic.
This reuses the real-flow equation and continuity, including integrability. -/
theorem left_characteristic {W : ℝ → ℝ} (hW : Continuous W) {y U : ℝ}
    (hy : y < W 0) (halive : ∀ s ∈ Ico 0 U, ∃ v, IsForwardSol W (y : ℂ) s v) :
    ∀ s ∈ Ico 0 U,
      (fwdMap W s y).re + W s < W s ∧
      ((fwdMap W s y).re + W s) - ((fwdMap W 0 y).re + W 0) =
        ∫ t in 0..s, 2 / (((fwdMap W t y).re + W t) - W t) ∧
      IntervalIntegrable (fun t => 2 / (((fwdMap W t y).re + W t) - W t)) volume 0 s := by
  intro s hs
  obtain ⟨v, hv⟩ := halive s hs
  obtain ⟨X, hXc, hXv, hX0, hXeq, hXi⟩ := Aux25.exists_real_of_isForwardSol hW hs.1 hv
  have hf : ∀ t ∈ Icc (0 : ℝ) s, (fwdMap W t y).re = X t := fun t ht => by
    rw [fwdMap_eq_of_isForwardSol hW hv ht, (hXv t ht).2, ofReal_re]
  have hneg := Aux25.pos_of_ne_zero_of_pos hXc.neg
    (fun t ht => neg_ne_zero.2 (hXv t ht).1) (show 0 < -X 0 by rw [hX0]; linarith only [hy])
  have heq := hXeq 0 ⟨le_rfl, hs.1⟩ s ⟨hs.1, le_rfl⟩ hs.1
  have he : (∫ t in (0 : ℝ)..s, 2 / (fwdMap W t y).re) = ∫ t in (0 : ℝ)..s, 2 / X t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [hf t (by rw [uIcc_of_le hs.1] at ht; exact ht)]
  refine ⟨by
    have hn : 0 < -X s := hneg s ⟨hs.1, le_rfl⟩
    rw [hf s ⟨hs.1, le_rfl⟩]
    linarith only [hn], ?_, ?_⟩
  · simp only [add_sub_cancel_right]
    rw [he, hf s ⟨hs.1, le_rfl⟩, hf 0 ⟨le_rfl, hs.1⟩]
    linarith only [heq]
  · simp only [add_sub_cancel_right]
    rw [intervalIntegrable_iff] at hXi ⊢
    refine hXi.congr_fun (fun t ht => ?_) measurableSet_uIoc
    rw [uIoc_of_le hs.1] at ht
    rw [hf t ⟨ht.1.le, ht.2⟩]

/-- Compose an initial chart's boundary value with a surviving real flow. -/
theorem tendsto_of_passive {W : ℝ → ℝ} (hW : Continuous W) {s y : ℝ} (hs : 0 ≤ s)
    (halive : ∃ v, IsForwardSol W (y : ℂ) s v)
    {D : Set ℂ} {F g : ℂ → ℂ} {p : ℂ}
    (hF : Tendsto F (𝓝[D] p) (𝓝[H] (y : ℂ)))
    (heq : EqOn g (fun z => fwdMap W s (F z) + W s) D) :
    Tendsto g (𝓝[D] p) (𝓝 (fwdMap W s y + W s)) := by
  obtain ⟨v, hv⟩ := halive
  have h := ((tendsto_fwdMap_of_isForwardSol hW hs hv).comp hF).add_const (W s : ℂ)
  rw [← fwdMap_eq_of_isForwardSol hW hv ⟨hs, le_rfl⟩] at h
  exact h.congr' (eventually_mem_nhdsWithin.mono fun z hz => (heq hz).symm)

/-- Read a real chart point by subtracting the second tip's hydrodynamic
boundary value. Both adherence hypotheses rule out empty boundary filters. -/
theorem chartPt_retFwd_of_tendsto {α β : ℝ≥0 → ℂ} {u r : ℝ≥0} {z : ℂ} {b x : ℝ}
    (hβ : β r ∈ closure (activeDomain α u β r))
    (hz : z ∈ closure (activeDomain α u β r))
    (hb : Tendsto (ConformalImage.mapOut (fillH (Restart.prefixSet α u β r)))
      (𝓝[activeDomain α u β r] (β r)) (𝓝 (b : ℂ)))
    (hx : Tendsto (ConformalImage.mapOut (fillH (Restart.prefixSet α u β r)))
      (𝓝[activeDomain α u β r] z) (𝓝 (x : ℂ))) :
    Sec7.Lemma76G.chartPt (retFwd α u β r) (activeDomain α u β r) z = x - b := by
  have : (𝓝[activeDomain α u β r] (β r)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hβ
  have : (𝓝[activeDomain α u β r] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hz
  have hlim : Tendsto (retFwd α u β r) (𝓝[activeDomain α u β r] z) (𝓝 ((x - b : ℝ) : ℂ)) := by
    unfold retFwd
    rw [hb.limUnder_eq, ofReal_sub]
    exact hx.sub_const _
  rw [Sec7.Lemma76G.chartPt, hlim.limUnder_eq, ofReal_re]

end InteractingSLE.RLC.G8Det
