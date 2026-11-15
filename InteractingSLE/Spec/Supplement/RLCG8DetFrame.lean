/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetSide

/-!
# G8's deterministic frame: assembly from the remaining chart estimate

Packet PROVE-G8-DET. The local conditional helper `exists_final_frame_of_gap`
supplies every clause of the requested frame from the two explicit remaining
inputs: exclusion of the second tip from the first completed hull, and the
eventual inequality between the two canonical chart points. It does not prove
`RLC.G8DetFrameStatement`.

`exists_final_activity_of_nonneg_real` proves the geometric clauses for the
source's left nonhitting sector, without assuming a chart estimate.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.RLC.G8Det

/-- The final approach, joint activity, and adherence of `1` follow from the
opposite-hull exclusion. All new input is visible in `hβout`. -/
theorem exists_final_activity {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hcop : Sec7.Prop74Order.IsCompleteOrderedPair α β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {σ r : ℝ≥0} {q : ℝ}
    (hsw : RealSwallowAt (fun s : ℝ => w s.toNNReal) 1 σ)
    (hq : 1 < q) (hασ : α σ = q) (hsmall : ∀ t ≤ r, ‖β t‖ < 1 / 2)
    (hβout : β r ∈ H \ fillH (α '' Icc 0 σ)) :
    ∃ t₀ : ℝ≥0, t₀ < σ ∧ ∀ u : ℝ≥0, t₀ < u → u < σ →
      α u ∈ H ∧ α u ∉ β '' Icc 0 r ∧ α u ∈ closure (activeDomain α u β r) ∧
        β r ∈ closure (activeDomain α u β r) ∧
        (∀ z ∈ Restart.prefixSet α u β r, z.im = 0 → z.re < 1) ∧
        (1 : ℂ) ∈ closure (activeDomain α u β r) := by
  obtain ⟨t₀, ht₀, happroach⟩ := exists_final_approach hcop.1 hcop.2.2.1
    hcop.2.2.2.2.1 hw hw0 hgen hsw hq hασ hsmall
  refine ⟨t₀, ht₀, fun u htu huσ => ?_⟩
  obtain ⟨_, hαout, hαoff⟩ := happroach u htu huσ
  have hβout' : β r ∈ H \ fillH (α '' Icc 0 u) :=
    Supp9D.H_diff_fillH_anti (image_mono (Icc_subset_Icc_right huσ.le)) hβout
  have hact := tips_mem_closure_of_opposite_hulls hcop hα0 hβ0 (u := u) (r := r)
  have hreal := real_prefix_re_lt_one hcop.1 hw hw0 hgen hsw huσ hsmall
  exact ⟨hαout.1, hαoff, hact.1 hαout, hact.2 hβout', hreal,
    one_mem_closure_activeDomain hcop.1 hcop.2.2.2.2.1 hreal⟩

/-- In the source's nonhitting left sector the opposite-hull exclusion, hence
all geometric clauses of the final frame, follow from the side lemma. -/
theorem exists_final_activity_of_nonneg_real {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hcop : Sec7.Prop74Order.IsCompleteOrderedPair α β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {σ r : ℝ≥0} {q : ℝ}
    (hsw : RealSwallowAt (fun s : ℝ => w s.toNNReal) 1 σ)
    (hq : 1 < q) (hασ : α σ = q) (hsmall : ∀ t ≤ r, ‖β t‖ < 1 / 2)
    (hβH : β r ∈ H) (hβoff : β r ∉ α '' Icc 0 σ)
    (hreal : ∀ t ≤ σ, (α t).im = 0 → 0 ≤ (α t).re) :
    ∃ t₀ : ℝ≥0, t₀ < σ ∧ ∀ u : ℝ≥0, t₀ < u → u < σ →
      α u ∈ H ∧ α u ∉ β '' Icc 0 r ∧ α u ∈ closure (activeDomain α u β r) ∧
        β r ∈ closure (activeDomain α u β r) ∧
        (∀ z ∈ Restart.prefixSet α u β r, z.im = 0 → z.re < 1) ∧
        (1 : ℂ) ∈ closure (activeDomain α u β r) :=
  exists_final_activity hcop hα0 hβ0 hw hw0 hgen hsw hq hασ hsmall
    (second_tip_outside_of_nonneg_real hcop hα0 hreal hβH hβoff)

/-- Conditional assembly with the exact two unresolved inputs displayed. The
requested statement itself is unchanged and is not asserted here. -/
theorem exists_final_frame_of_gap {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hcop : Sec7.Prop74Order.IsCompleteOrderedPair α β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {σ r : ℝ≥0} {q ε : ℝ}
    (hsw : RealSwallowAt (fun s : ℝ => w s.toNNReal) 1 σ)
    (hq : 1 < q) (hασ : α σ = q) (hsmall : ∀ t ≤ r, ‖β t‖ < 1 / 2)
    (hβout : β r ∈ H \ fillH (α '' Icc 0 σ))
    (hgap : ∃ t₁ : ℝ≥0, t₁ < σ ∧ ∀ u : ℝ≥0, t₁ < u → u < σ →
      0 < Sec7.Lemma76G.chartPt (retFwd α u β r) (activeDomain α u β r) (α u) ∧
      Sec7.Lemma76G.chartPt (retFwd α u β r) (activeDomain α u β r) 1 <
        (1 + ε) * Sec7.Lemma76G.chartPt (retFwd α u β r) (activeDomain α u β r) (α u)) :
    ∃ t₀ : ℝ≥0, t₀ < σ ∧ ∀ u : ℝ≥0, t₀ < u → u < σ →
      α u ∈ H ∧ α u ∉ β '' Icc 0 r ∧ α u ∈ closure (activeDomain α u β r) ∧
        β r ∈ closure (activeDomain α u β r) ∧ IsFrameGap ε α u β r := by
  obtain ⟨t₀, ht₀, hact⟩ := exists_final_activity hcop hα0 hβ0 hw hw0 hgen hsw hq hασ hsmall hβout
  obtain ⟨t₁, ht₁, hgap⟩ := hgap
  refine ⟨max t₀ t₁, max_lt ht₀ ht₁, fun u htu huσ => ?_⟩
  obtain ⟨hH, hoff, hclα, hclβ, hreal, hcl1⟩ :=
    hact u ((le_max_left _ _).trans_lt htu) huσ
  exact ⟨hH, hoff, hclα, hclβ, hreal, hcl1,
    hgap u ((le_max_right _ _).trans_lt htu) huσ⟩

/-- A tip trapped by an earlier individual prefix cannot be active for a
later joint prefix. This makes the opposite-hull obstruction precise. -/
theorem not_mem_closure_activeDomain_of_trapped {α β : ℝ≥0 → ℂ}
    (hα : Continuous α) (hβ : Continuous β) {a u r : ℝ≥0} (hau : a ≤ u)
    (htrap : HalfPlaneSep.IsTrappedAt (α '' Icc 0 a) (β r)) :
    β r ∉ closure (activeDomain α u β r) := by
  have hc : IsCompact (Restart.prefixSet α u β r) :=
    (isCompact_Icc.image hα).union (isCompact_Icc.image hβ)
  have hsub : activeDomain α u β r ⊆ H \ fillH (α '' Icc 0 a) := by
    rw [Restart.activeDomain_eq hc.isClosed]
    exact Supp9D.H_diff_fillH_anti
      ((image_mono (Icc_subset_Icc_right hau)).trans subset_union_left)
  obtain ⟨δ, hδ, hd⟩ := htrap
  intro hcl
  obtain ⟨z, hz, hzr⟩ := Metric.mem_closure_iff.1 hcl δ hδ
  exact Set.disjoint_left.1 hd (by rw [mem_ball, dist_comm]; exact hzr) (hsub hz)

/-- A sample satisfying the requested premises and having its second tip
already trapped before `σ` refutes the requested universal statement. This is
a conditional obstruction; no such sample is constructed in this file. -/
theorem not_g8DetFrameStatement_of_trapped {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hcop : Sec7.Prop74Order.IsCompleteOrderedPair α β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {σ r a : ℝ≥0} {q : ℝ}
    (hsw : RealSwallowAt (fun s : ℝ => w s.toNNReal) 1 σ)
    (hq : 1 < q) (hασ : α σ = q) (hβH : β r ∈ H)
    (hβoff : β r ∉ α '' Icc 0 σ) (hsmall : ∀ t ≤ r, ‖β t‖ < 1 / 2)
    (ha : a < σ) (htrap : HalfPlaneSep.IsTrappedAt (α '' Icc 0 a) (β r)) :
    ¬ G8DetFrameStatement := by
  intro hframe
  obtain ⟨t₀, ht₀, hfinal⟩ := hframe α β w σ r q 1 one_pos hcop hα0 hβ0
    hw hw0 hgen hsw hq hασ hβH hβoff hsmall
  obtain ⟨u, hmu, huσ⟩ := exists_between (max_lt ht₀ ha)
  have hcl := (hfinal u ((le_max_left _ _).trans_lt hmu) huσ).2.2.2.1
  exact not_mem_closure_activeDomain_of_trapped hcop.1 hcop.2.2.2.2.1
    ((le_max_right _ _).trans hmu.le) htrap hcl

end InteractingSLE.RLC.G8Det
