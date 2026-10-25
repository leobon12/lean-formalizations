import SupercriticalLQGUniqueness.B2.PfeLocal.L2RationalFinite

 

















set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 
def l4Fill (K : Set ℂ) : Set ℂ :=
  {p | ∀ S : Set ℂ, IsPreconnected S → S ⊆ Kᶜ → p ∈ S → Bornology.IsBounded S}

theorem l4_subset_fill (K : Set ℂ) : K ⊆ l4Fill K := fun p hp S _ hSK hpS =>
  absurd hp (hSK hpS)

theorem l4_fill_frontier {K T : Set ℂ} (hT : IsPreconnected T)
    (h1 : (T ∩ l4Fill K).Nonempty) (h2 : (T \ l4Fill K).Nonempty) : (T ∩ K).Nonempty := by
  by_contra hTK
  rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hTK
  obtain ⟨p, hpT, hpF⟩ := h1
  obtain ⟨q, hqT, hqF⟩ := h2
  simp only [l4Fill, mem_ofPred_eq, not_forall] at hqF
  obtain ⟨S, hS, hSK, hqS, hSb⟩ := hqF
  have hU : IsPreconnected (T ∪ S) := hT.union q hqT hqS hS
  have hUK : T ∪ S ⊆ Kᶜ := union_subset (fun x hx => Set.disjoint_left.1 hTK hx) hSK
  exact hSb ((hpF (T ∪ S) hU hUK (Or.inl hpT)).subset subset_union_right)

theorem l4_fill_mono {K₁ K₂ : Set ℂ} (h : K₁ ⊆ l4Fill K₂) : l4Fill K₁ ⊆ l4Fill K₂ := by
  intro p hp S hS hSK hpS
  by_contra hb
  have hSK₁ : S ⊆ K₁ᶜ := by
    intro s hsS hsK
    exact hb ((h hsK) S hS hSK hsS)
  exact hb (hp S hS hSK₁ hpS)

theorem l4_fill_subset_closedBall {K : Set ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (h : K ⊆ closedBall c R) :
    l4Fill K ⊆ closedBall c R := by
  intro p hp
  by_contra hpc
  rw [mem_closedBall, not_le] at hpc
  set S : Set ℂ := (fun t : ℝ => p + (t : ℂ) * (p - c)) '' Ici 0 with hSdef
  have hS : IsPreconnected S :=
    isPreconnected_Ici.image _ (by fun_prop : Continuous fun t : ℝ => p + (t : ℂ) * (p - c)).continuousOn
  have hnorm : ∀ t : ℝ, 0 ≤ t → dist (p + (t : ℂ) * (p - c)) c = (1 + t) * dist p c := by
    intro t ht
    rw [dist_eq_norm, dist_eq_norm, show p + (t : ℂ) * (p - c) - c = ((1 + t : ℝ) : ℂ) * (p - c)
      by push_cast; ring, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  have hSK : S ⊆ Kᶜ := by
    rintro _ ⟨t, ht, rfl⟩ hK
    have := mem_closedBall.1 (h hK)
    rw [hnorm t ht] at this
    have hdc : 0 < dist p c := lt_of_le_of_lt hR hpc
    nlinarith [mem_Ici.1 ht]
  have hpS : p ∈ S := ⟨0, mem_Ici.2 le_rfl, by simp⟩
  have hb := hp S hS hSK hpS
  obtain ⟨M, hM⟩ := hb.subset_closedBall c
  have hdc : 0 < dist p c := lt_of_le_of_lt hR hpc
  obtain ⟨t, ht⟩ := exists_nat_gt (M / dist p c)
  have hmem := hM ⟨(t : ℝ), mem_Ici.2 (by positivity), rfl⟩
  rw [mem_closedBall, hnorm _ (by positivity)] at hmem
  rw [div_lt_iff₀ hdc] at ht
  nlinarith

 

theorem l4_meets_of_disconnects {K : Set ℂ} {w : ℂ} {r : ℝ}
    (hdisc : Disconnects K (sphere w r) (sphere w (2 * r))) {T : Set ℂ} (hT : IsPreconnected T)
    (h1 : (T ∩ closedBall w r).Nonempty) (h2 : (T \ ball w (2 * r)).Nonempty) :
    (T ∩ K).Nonempty := by
  by_contra hTK
  rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hTK
  apply hdisc
  refine ⟨T, hT, fun x hx => Set.disjoint_left.1 hTK hx, ?_, ?_⟩
  all_goals
    obtain ⟨p, hpT, hp⟩ := h1
    obtain ⟨q, hqT, hq⟩ := h2
    have hI := (hT.image (fun x => dist x w) (continuous_id.dist continuous_const).continuousOn)
    have hp' : dist p w ≤ r := mem_closedBall.1 hp
    have hq' : 2 * r ≤ dist q w := not_lt.1 (fun h => hq (mem_ball.2 h))
  · have hmem : r ∈ (fun x => dist x w) '' T :=
      hI.Icc_subset ⟨p, hpT, rfl⟩ ⟨q, hqT, rfl⟩ ⟨hp', by
        have := dist_nonneg (x := p) (y := w); linarith⟩
    obtain ⟨x, hxT, hx⟩ := hmem
    exact ⟨x, hxT, mem_sphere.2 hx⟩
  · have hmem : 2 * r ∈ (fun x => dist x w) '' T :=
      hI.Icc_subset ⟨p, hpT, rfl⟩ ⟨q, hqT, rfl⟩ ⟨by
        have := dist_nonneg (x := p) (y := w); linarith, hq'⟩
    obtain ⟨x, hxT, hx⟩ := hmem
    exact ⟨x, hxT, mem_sphere.2 hx⟩

theorem l4_closedBall_subset_fill {K : Set ℂ} {w : ℂ} {r : ℝ}
    (hdisc : Disconnects K (sphere w r) (sphere w (2 * r))) :
    closedBall w r ⊆ l4Fill K := by
  intro p hp S hS hSK hpS
  by_contra hb
  have hout : (S \ ball w (2 * r)).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at hne
    exact hb (isBounded_ball.subset hne)
  obtain ⟨x, hxS, hxK⟩ := l4_meets_of_disconnects hdisc hS ⟨p, hpS, hp⟩ hout
  exact hSK hxS hxK

end SupercriticalLQGUniqueness.B2.PfeLocal
