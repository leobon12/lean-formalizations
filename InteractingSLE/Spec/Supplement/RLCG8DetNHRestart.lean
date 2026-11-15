/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetNH

/-!
# The final fresh segment lies in each late joint domain

Packet PROVE-G8-DET, R63. This supplies the physical-domain part of the late
relative-chain construction: after any sufficiently late cut, the remaining
open segment of α is in the retained joint unbounded domain and its terminal
point is adherent and off the retained union.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.RLC.G8Det

/-- The final open segment of α stays in every sufficiently late retained
joint domain. In particular a relative chart is needed only after a late cut,
not across earlier contacts of α with the β prefix. -/
theorem exists_final_restart_domain {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hcop : Sec7.Prop74Order.IsCompleteOrderedPair α β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {σ r : ℝ≥0} {q : ℝ}
    (hsw : RealSwallowAt (fun s : ℝ => w s.toNNReal) 1 σ)
    (hq : 1 < q) (hασ : α σ = q) (hsmall : ∀ t ≤ r, ‖β t‖ < 1 / 2)
    (hβH : β r ∈ H) (hβoff : β r ∉ α '' Icc 0 σ)
    (hNH : ∀ t < σ, (α t).im = 0 → 0 ≤ (α t).re) :
    ∃ t₀ : ℝ≥0, t₀ < σ ∧ ∀ a : ℝ≥0, t₀ < a → a < σ →
      α a ∈ H ∧ β r ∈ closure (activeDomain α a β r) ∧
        α σ ∈ closure (activeDomain α a β r) ∧ α σ ∉ Restart.prefixSet α a β r ∧
        ∀ u ∈ Ioo a σ, α u ∈ activeDomain α a β r := by
  obtain ⟨t₀, ht₀, hact⟩ := exists_final_activity_of_nonneg_real hcop hα0 hβ0 hw hw0 hgen
    hsw hq hασ hsmall hβH hβoff (nonneg_real_le_of_before hNH hq hασ)
  refine ⟨t₀, ht₀, fun a hta haσ => ?_⟩
  obtain ⟨hHa, _, _, hclβ, hreal, _⟩ := hact a hta haσ
  have hc : IsCompact (Restart.prefixSet α a β r) :=
    (isCompact_Icc.image hcop.1).union (isCompact_Icc.image hcop.2.2.2.2.1)
  have hfuture : ∀ u ∈ Ioo a σ, α u ∈ activeDomain α a β r := by
    intro u hu
    obtain ⟨hHu, hoffβ, hclu, _, _, _⟩ := hact u (hta.trans hu.1) hu.2
    have hcu : IsCompact (Restart.prefixSet α u β r) :=
      (isCompact_Icc.image hcop.1).union (isCompact_Icc.image hcop.2.2.2.2.1)
    have hsub : activeDomain α u β r ⊆ activeDomain α a β r := by
      rw [Restart.activeDomain_eq hc.isClosed, Restart.activeDomain_eq hcu.isClosed]
      exact Supp9D.H_diff_fillH_anti
        (union_subset_union_left _ (image_mono (Icc_subset_Icc_right hu.1.le)))
    have hoff : α u ∉ Restart.prefixSet α a β r := by
      rintro (⟨t, ht, hte⟩ | hβmem)
      · exact hu.1.not_ge (hcop.2.1 hte ▸ ht.2)
      · exact hoffβ hβmem
    have hclold := closure_mono hsub hclu
    rw [Restart.activeDomain_eq hc.isClosed] at hclold
    have hfree := Sec7.isFreeAt_of_mem_closure hc.isClosed hoff hclold
    rw [Restart.activeDomain_eq hc.isClosed]
    exact Sec7.mem_H_diff_fillH_of_isFreeAt hfree hHu
  have hclσ : α σ ∈ closure (activeDomain α a β r) := by
    have hne : (𝓝[Ioo a σ] σ).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo haσ.ne]
      exact ⟨haσ.le, le_rfl⟩
    have hlim : Tendsto α (𝓝[Ioo a σ] σ) (𝓝 (α σ)) :=
      hcop.1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact mem_closure_of_tendsto hlim
      (eventually_mem_nhdsWithin.mono fun u hu => hfuture u hu)
  have hoffσ : α σ ∉ Restart.prefixSet α a β r := by
    intro hmem
    have hlt := hreal (α σ) hmem (by rw [hασ]; exact ofReal_im q)
    rw [hασ, ofReal_re] at hlt
    exact hq.not_gt hlt
  exact ⟨hHa, hclβ, hclσ, hoffσ, hfuture⟩

end InteractingSLE.RLC.G8Det
