/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetLateShift
import InteractingSLE.Spec.Sec7.ReverseArcSide

/-!
# G8: physical separation and the filled collar at the new real contact

Packet PROVE-G8-DET. The completed α prefix joins `0` to `q > 1` and misses
`1`, so the landed planar trapping lemma supplies the required upper collar.
The late trace is confined near `q`, while the entire β filling stays small.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.RLC.G8Det.Late

theorem exists_final_ball {α : ℝ≥0 → ℂ} (hc : Continuous α) {σ : ℝ≥0}
    (hσ : 0 < σ) {q δ : ℝ} (hασ : α σ = q) (hδ : 0 < δ) :
    ∃ a < σ, α '' Icc a σ ⊆ ball (q : ℂ) δ := by
  have hev : ∀ᶠ u in 𝓝[<] σ, α u ∈ ball (q : ℂ) δ :=
    (hασ ▸ hc.continuousAt.tendsto).mono_left nhdsWithin_le_nhds |>.eventually (ball_mem_nhds _ hδ)
  obtain ⟨t, ht, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hσ).1 hev
  obtain ⟨a, hta, haσ⟩ := exists_between (show t < σ from ht)
  refine ⟨a, haσ, ?_⟩
  rintro z ⟨u, hu, rfl⟩
  rcases hu.2.eq_or_lt with he | he
  · rw [he, hασ]; exact mem_ball_self hδ
  · exact hsub ⟨hta.trans_le hu.1, he⟩

theorem small_prefix_fill {β : ℝ≥0 → ℂ} (hc : Continuous β) {r : ℝ≥0}
    (hsmall : ∀ t ≤ r, ‖β t‖ < 1 / 2) :
    closure (fillH (β '' Icc 0 r)) ⊆ closedBall 0 (1 / 2 : ℝ) := by
  apply closure_minimal _ isClosed_closedBall
  apply fillH_subset_closedBall_zero
  rw [(isCompact_Icc.image hc).isClosed.closure_eq]
  rintro z ⟨t, ht, rfl⟩
  exact mem_closedBall_zero_iff.2 (hsmall t ht.2).le

/-- The late trace, including its endpoint, is physically separated from
the entire closed filling of the small second prefix. -/
theorem exists_final_disjoint_small_fill {α β : ℝ≥0 → ℂ}
    (hcα : Continuous α) (hcβ : Continuous β) {σ r : ℝ≥0} {q : ℝ}
    (hσ : 0 < σ) (hq : 1 < q) (hασ : α σ = q) (hsmall : ∀ t ≤ r, ‖β t‖ < 1 / 2) :
    ∃ a < σ, Disjoint (closure (α '' Icc a σ)) (closure (fillH (β '' Icc 0 r))) := by
  obtain ⟨a, ha, hball⟩ := exists_final_ball hcα hσ hασ (show (0 : ℝ) < 1 / 4 by norm_num)
  refine ⟨a, ha, (closedBall_disjoint_closedBall (x := (q : ℂ)) (y := 0)
    (δ := (1 / 4 : ℝ)) (ε := (1 / 2 : ℝ)) ?_).mono
      (closure_minimal (hball.trans ball_subset_closedBall) isClosed_closedBall)
      (small_prefix_fill hcβ hsmall)⟩
  rw [dist_zero_right, norm_real, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans hq)]
  linarith only [hq]

/-- Every earlier real contact is left of `1`, and the new endpoint is `q > 1`;
in particular `1` is not an old real trace point at completion. -/
theorem one_notMem_completed_prefix {α : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hc : Continuous α) (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {σ : ℝ≥0} {q : ℝ} (hsw : RealSwallowAt (fun s : ℝ => w s.toNNReal) 1 σ)
    (hq : 1 < q) (hασ : α σ = q) : (1 : ℂ) ∉ α '' Icc 0 σ := by
  rintro ⟨t, ht, he⟩
  rcases ht.2.eq_or_lt with h | h
  · rw [h, hασ] at he
    have hq1 : q = 1 := by exact_mod_cast he
    exact hq.ne' hq1
  · have hlt := re_lt_one_of_real_before_swallow hc hw hw0 hgen hsw h (by rw [he]; rfl)
    simp only [he, one_re, lt_self_iff_false] at hlt

/-- The source's Jordan filling collar, by the landed connected-set trapping
theorem. No boundary collision or collar is assumed. -/
theorem completed_own_collar {α : ℝ≥0 → ℂ} (hc : Continuous α)
    (hH : ∀ t, 0 ≤ (α t).im) (hα0 : α 0 = 0) {σ : ℝ≥0} {q : ℝ}
    (hq : 1 < q) (hασ : α σ = q) (hoff : (1 : ℂ) ∉ α '' Icc 0 σ) :
    ∃ δ > 0, ∀ z : ℂ, z ∈ H → ‖z - 1‖ < δ → z ∈ ownHull α σ := by
  have htrap := Sec7.isTrappedAt_of_isPreconnected (isCompact_Icc.image hc)
    (isPreconnected_Icc.image _ hc.continuousOn)
    (by rintro z ⟨t, _, rfl⟩; exact hH t)
    (u := 0) (v := q) (y := 1) ⟨0, ⟨le_rfl, zero_le⟩, hα0⟩
    ⟨σ, ⟨zero_le, le_rfl⟩, hασ⟩ zero_lt_one hq hoff
  obtain ⟨δ, hδ, hdis⟩ := htrap
  refine ⟨δ, hδ, fun z hz hdist => ?_⟩
  by_contra h
  exact Set.disjoint_left.1 hdis (mem_ball.2 (by simpa only [dist_eq_norm, ofReal_one] using hdist)) ⟨hz, h⟩

/-- The retained interior tip misses the closure of the completed own hull. -/
theorem beta_notMem_closure_ownHull {α β : ℝ≥0 → ℂ}
    (hcop : Sec7.Prop74Order.IsCompleteOrderedPair α β) (hα0 : α 0 = 0)
    {σ r : ℝ≥0} {q : ℝ} (hq : 1 < q) (hασ : α σ = q)
    (hNH : ∀ t < σ, (α t).im = 0 → 0 ≤ (α t).re)
    (hβH : β r ∈ H) (hβoff : β r ∉ α '' Icc 0 σ) : β r ∉ closure (ownHull α σ) := by
  have hout := second_tip_outside_of_no_negative_contact hcop hα0 hq hασ hNH hβH hβoff
  exact fun hcl => hout.2 ((isHPHull_ownHull hcop.1 hα0 σ).mem_of_mem_closure hβH hcl)

end InteractingSLE.RLC.G8Det.Late
