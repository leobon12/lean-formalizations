/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51GQ
import InteractingSLE.Spec.Sec6.Aux36Lift
import InteractingSLE.Spec.Supplement.G7ClockCluster

/-!
# Prime-end limits of the chart-Q excursions in Proposition 5.1

The finite endpoint lemma reuses `Sec6.exists_tendsto_lift`. At infinite original
time the inverted proper arc tends to zero; `Supp7`'s cluster-set theorem gives
the corresponding finite real mapping-out limit. Inverting that limit gives a
finite nonzero `revChart` limit unless the physical endpoint is the counterflow
tip. No simplicity of the counterflow or determination theorem is used.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Sec5.Prop51HTopo

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G

variable {w : ℝ → ℝ} {β η α : ℝ → ℂ} {s a b : ℝ}

/-- A path tending to a finite boundary point has a unique real mapping-out
limit, even when its original parameter tends to infinity. -/
theorem exists_tendsto_fwdMap_atTop (hβ : IsLoewnerTrace w β)
    (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    (hc : ContinuousOn α (Ioi a))
    (hD : ∀ t ∈ Ioi a, α t ∈ H \ fwdHull w s) {z : ℂ}
    (hlim : Tendsto α atTop (𝓝 z)) (hz : z ∉ H \ fwdHull w s) :
    ∃ x : ℝ, extendFrom H (fwdMapInv w s) x = z ∧
      Tendsto (fun t => fwdMap w s (α t)) atTop (𝓝 (x : ℂ)) := by
  let G : ℝ → ℂ := fun t => fwdMap w s (α t)
  let F : ℂ → ℂ := extendFrom H (fwdMapInv w s)
  obtain ⟨hFd, hFc, hFi, hFR⟩ := hβ.fiber_hyps hw hw0 hs
  have hGH : ∀ t ∈ Ioi a, G t ∈ H := fun t ht =>
    QuantumZipper.FwdHolo.mapsTo_fwdMap hw hs (hD t ht)
  have hFG : ∀ t ∈ Ioi a, F (G t) = α t := by
    intro t ht
    rw [show F (G t) = fwdMapInv w s (G t) from
      extendFrom_fwdMapInv_eq hw hw0 hs (hGH t ht)]
    exact QuantumZipper.RS.fwdMapInv_fwdMap hw hw0 hs (hD t ht)
  have hGc : ContinuousOn G (Ioi a) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hw hs).continuousOn.comp hc hD
  obtain ⟨C, _, hC⟩ := exists_norm_fwdMap_sub_le hw hw0 hs
  have hαB : ∀ᶠ t in atTop, ‖α t‖ ≤ ‖z‖ + 1 := by
    filter_upwards [hlim.eventually (closedBall_mem_nhds z one_pos)] with t ht
    have hnorm := norm_le_norm_add_norm_sub' (α t) z
    rw [dist_eq_norm] at ht
    linarith only [hnorm, ht]
  have hGB : ∀ᶠ t in atTop, ‖G t‖ ≤ ‖z‖ + 1 + C := by
    filter_upwards [eventually_gt_atTop a, hαB] with t ht htB
    have hnorm := norm_le_norm_add_norm_sub' (G t) (α t)
    have hdist := hC (α t) (hD t ht)
    change ‖G t - α t‖ ≤ C at hdist
    linarith only [hnorm, hdist, htB]
  obtain ⟨ξ, hξH, hFξ, hξ⟩ := Supp7.exists_tendsto_of_tendsto_comp_filter
    hFd hFc hFi hFR
    (show ∀ᶠ t in atTop, G t ∈ Hbar from
      (eventually_gt_atTop a).mono fun t ht => H_subset_Hbar (hGH t ht)) hGB
    (fun U hU => by
      obtain ⟨c, hcU⟩ := eventually_atTop.1 hU
      exact ⟨Ioi (max a c), Ioi_mem_atTop _,
        fun t ht => hcU t ((le_max_right a c).trans ht.le), isPreconnected_Ioi,
        hGc.mono fun t ht => (le_max_left a c).trans_lt ht⟩)
    (hlim.congr' ((eventually_gt_atTop a).mono fun t ht => (hFG t ht).symm))
  have hξim : ξ.im = 0 := by
    refine le_antisymm (not_lt.1 fun hξpos => hz ?_) hξH
    rw [← hFξ, extendFrom_fwdMapInv_eq hw hw0 hs hξpos]
    exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hw hw0 hs hξpos
  have hξreal := eq_ofReal_re_of_im_eq_zero hξim
  exact ⟨ξ.re, hξreal ▸ hFξ, hξreal ▸ hξ⟩

/-- Every finite excursion endpoint other than the counterflow tip has a finite
nonzero real limit in the counterflow chart. Filled hull interiors are allowed. -/
theorem exists_tendsto_revChart_left (hη : IsProperArc η)
    (hβ : IsLoewnerTrace w β) (hw : Continuous w) (hw0 : w 0 = 0)
    (hs : 0 ≤ s) (ha : 0 < a) (hab : a < b)
    (hD : ∀ t ∈ Ico a b, η t ∈ H \ cfHullQ w s)
    (hb : η b ∉ H \ cfHullQ w s) (htip : η b ≠ negInv (β s)) :
    ∃ x : ℝ, x ≠ 0 ∧
      Tendsto (fun t => revChart w s (η t)) (𝓝[<] b) (𝓝 (x : ℂ)) := by
  have hαc : ContinuousOn (fun t => negInv (η t)) (Icc a b) :=
    continuousOn_negInv.comp
      (hη.cont.mono fun t ht => ha.le.trans ht.1)
      (fun t ht => hη.mem_H t (ha.trans_le ht.1))
  have hαb : negInv (η b) ∉ H \ fwdHull w s := by
    intro h
    apply hb
    refine ⟨hη.mem_H b (ha.trans hab), ?_⟩
    rintro ⟨z, hz, he⟩
    apply h.2
    rw [← he, negInv_negInv']
    exact hz
  obtain ⟨q, hq, hlim⟩ := Sec6.exists_tendsto_lift hβ hw hw0 hs hab hαc
    (fun t ht => negInv_notMem_fwdHull (hD t ht)) hαb
  rw [YuanSimpleApprox.trMap_zero_left hw0] at hq
  have hq0 : q ≠ 0 := by
    intro hqzero
    rw [hqzero, Complex.ofReal_zero, extendFrom_zero hβ hw hw0 hs] at hq
    apply htip
    have hinv := congrArg negInv hq
    rw [negInv_negInv'] at hinv
    exact hinv.symm
  refine ⟨-q⁻¹, neg_ne_zero.2 (inv_ne_zero hq0), ?_⟩
  have hinv := (continuousAt_negInv (Complex.ofReal_ne_zero.2 hq0)).tendsto.comp hlim
  simpa only [revChart, negInv, Complex.ofReal_neg, Complex.ofReal_inv,
    Function.comp_def] using hinv

/-- An infinite tail of a proper arc in the complementary domain converges to
a finite nonzero real prime end in the counterflow chart. -/
theorem exists_tendsto_revChart_atTop (hη : IsProperArc η)
    (hβ : IsLoewnerTrace w β) (hw : Continuous w) (hw0 : w 0 = 0)
    (hs : 0 ≤ s) (hβs : β s ≠ 0) (ha : 0 ≤ a)
    (hD : ∀ t ∈ Ioi a, η t ∈ H \ cfHullQ w s) :
    ∃ x : ℝ, x ≠ 0 ∧
      Tendsto (fun t => revChart w s (η t)) atTop (𝓝 (x : ℂ)) := by
  have hαc : ContinuousOn (fun t => negInv (η t)) (Ioi a) :=
    continuousOn_negInv.comp
      (hη.cont.mono fun t ht => (ha.trans ht.le))
      (fun t ht => hη.mem_H t (ha.trans_lt ht))
  have hαlim : Tendsto (fun t => negInv (η t)) atTop (𝓝 (0 : ℂ)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [norm_negInv, Function.comp_def] using
      tendsto_inv_atTop_zero.comp hη.tendsto
  obtain ⟨q, hq, hlim⟩ := exists_tendsto_fwdMap_atTop hβ hw hw0 hs hαc
    (fun t ht => negInv_notMem_fwdHull (hD t ht)) hαlim
    (fun h => ne_zero_of_mem_H h.1 rfl)
  have hq0 : q ≠ 0 := by
    intro hqzero
    rw [hqzero, Complex.ofReal_zero, extendFrom_zero hβ hw hw0 hs] at hq
    exact hβs hq
  refine ⟨-q⁻¹, neg_ne_zero.2 (inv_ne_zero hq0), ?_⟩
  have hinv := (continuousAt_negInv (Complex.ofReal_ne_zero.2 hq0)).tendsto.comp hlim
  simpa only [revChart, negInv, Complex.ofReal_neg, Complex.ofReal_inv,
    Function.comp_def] using hinv

end InteractingSLE.Sec5.Prop51HTopo
