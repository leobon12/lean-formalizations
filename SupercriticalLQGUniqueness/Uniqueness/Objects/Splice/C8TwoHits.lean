import SupercriticalLQGUniqueness.Uniqueness.Objects.Compare.SupGoodSeparator
import SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow.Endpoint



 
set_option autoImplicit false
noncomputable section
open Set Metric
namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Splice

 

theorem separator_two_hits {P : ℝ → ℂ} {a t b r R : ℝ} {y : ℂ} {K : Set ℂ}
    (hat : a < t) (htb : t < b) (hrR : r ≤ R)
    (hP : ContinuousOn P (Icc a b))
    (hsep : LQGMetric.Disconnects K (sphere y r) (sphere y R))
    (ha : P a ∈ (ball y R)ᶜ) (hb : P b ∈ (ball y R)ᶜ)
    (ht : P t ∈ closedBall y r) (htK : P t ∉ K) :
    ∃ t₁ t₂ : ℝ, a ≤ t₁ ∧ t₁ < t ∧ t < t₂ ∧ t₂ ≤ b ∧
      P t₁ ∈ K ∧ P t₂ ∈ K := by
  have hsep' := LQGMetric.Disconnects.closedBall_compl_ball hrR hsep
  have hleft := hsep'.symm (P a) (P t)
    (LQGMetric.pathOfIcc P hat.le (hP.mono (Icc_subset_Icc le_rfl htb.le))) ha ht
  obtain ⟨u, huRange, huK⟩ := hleft
  obtain ⟨t₁, ht₁, hut₁⟩ :=
    LQGMetric.range_pathOfIcc_subset P hat.le
      (hP.mono (Icc_subset_Icc le_rfl htb.le)) huRange
  have ht₁K : P t₁ ∈ K := hut₁ ▸ huK
  have ht₁lt : t₁ < t := lt_of_le_of_ne ht₁.2
    (fun heq => htK (heq ▸ ht₁K))
  have hright := hsep' (P t) (P b)
    (LQGMetric.pathOfIcc P htb.le (hP.mono (Icc_subset_Icc hat.le le_rfl))) ht hb
  obtain ⟨v, hvRange, hvK⟩ := hright
  obtain ⟨t₂, ht₂, hvt₂⟩ :=
    LQGMetric.range_pathOfIcc_subset P htb.le
      (hP.mono (Icc_subset_Icc hat.le le_rfl)) hvRange
  have ht₂K : P t₂ ∈ K := hvt₂ ▸ hvK
  have htt₂ : t < t₂ := lt_of_le_of_ne ht₂.1
    (fun heq => htK (heq.symm ▸ ht₂K))
  exact ⟨t₁, t₂, ht₁.1, ht₁lt, htt₂, ht₂.2, ht₁K, ht₂K⟩

end SupercriticalLQGUniqueness.Uniqueness.Objects.Splice
