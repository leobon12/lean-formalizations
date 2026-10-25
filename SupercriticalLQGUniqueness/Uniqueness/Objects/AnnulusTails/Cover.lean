import SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Tour
import SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEventContact.Contact
import SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEventSeparator.Separator
import SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent.EventPredicate




 



























set_option autoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails

 

theorem path_meets_sphere {x z y : ℂ} (γ : Path x z) {ρ₁ ρ ρ₂ : ℝ} (hx : dist x y = ρ₁)
    (hz : dist z y = ρ₂) (h₁ : ρ₁ ≤ ρ) (h₂ : ρ ≤ ρ₂) : (range γ ∩ sphere y ρ).Nonempty := by
  have hf : Continuous fun t : unitInterval => dist (γ t) y := γ.continuous.dist continuous_const
  have hmem : ρ ∈ Icc ((fun t : unitInterval => dist (γ t) y) 0)
      ((fun t : unitInterval => dist (γ t) y) 1) := by
    simp only [Path.source, Path.target, hx, hz]
    exact ⟨h₁, h₂⟩
  obtain ⟨t, ht⟩ := intermediate_value_univ 0 1 hf hmem
  exact ⟨γ t, ⟨t, rfl⟩, by simpa only [mem_sphere] using ht⟩

 


theorem around_le_of_loop_cover (D : LSCMetric) {y : ℂ} {ρ₁ ρ ρ₂ : ℝ} (h₁ : ρ₁ < ρ)
    (h₂ : ρ < ρ₂) (hρ : 0 < ρ) (W : Finset ℂ) (t : ℂ → ℝ) (ht : ∀ w ∈ W, 0 < t w)
    (P : ℂ → ℝ → ℂ) (a b : ℂ → ℝ) (hP : ∀ w ∈ W, D.IsCurve (P w) (a w) (b w))
    (hPA : ∀ w ∈ W, P w '' Icc (a w) (b w) ⊆ Objects.CorrectedEvent.ann w (t w) (2 * t w))
    (hPD : ∀ w ∈ W, LQGMetric.Disconnects (P w '' Icc (a w) (b w))
      (sphere w (t w)) (sphere w (2 * t w)))
    (hcov : ∀ x ∈ sphere y ρ, ∃ w ∈ W, dist x w < t w)
    (hin : ∀ w ∈ W, closedBall w (2 * t w) ⊆ Objects.CorrectedEvent.ann y ρ₁ ρ₂) :
    Objects.CorrectedEvent.around D y ρ₁ ρ₂ ≤ 2 * ∑ w ∈ W, D.len (P w) (a w) (b w) := by
  classical
  
  let ι := {w // w ∈ W}
  let T : ι → Set ℂ := fun i => P i '' Icc (a i) (b i)
  let V : ι → Set ℂ := fun i => connectedComponentIn (T i)ᶜ (i : ℂ)
  have hcont : ∀ i : ι, ContinuousOn (P i) (Icc (a i) (b i)) := fun i =>
    (hP i i.2).continuousOn_of_mapsTo (isCompact_closedBall (i : ℂ) (2 * t i))
      (fun s hs => by
        have hs' := hPA i i.2 ⟨s, hs, rfl⟩
        exact (mem_closedBall).2 (le_of_lt hs'.2))
  have hTcpt : ∀ i : ι, IsCompact (T i) := fun i => isCompact_Icc.image_of_continuousOn (hcont i)
  have hTc : ∀ i : ι, IsClosed (T i) := fun i => (hTcpt i).isClosed
  have hTp : ∀ i : ι, IsPreconnected (T i) := fun i => isPreconnected_Icc.image _ (hcont i)
  have hTn : ∀ i : ι, (T i).Nonempty := fun i => ⟨P i (a i), a i, left_mem_Icc.2 (hP i i.2).1, rfl⟩
  have hVball : ∀ i : ι, ball (i : ℂ) (t i) ⊆ V i ∧ V i ⊆ ball (i : ℂ) (2 * t i) := fun i =>
    Objects.CorrectedEventSeparator.ball_subset_component_subset_ball (hTc i) (ht i i.2) (hPA i i.2) (hPD i i.2)
  have hVb : ∀ i : ι, Bornology.IsBounded (V i) := fun i =>
    isBounded_ball.subset (hVball i).2
  
  have hScov : sphere y ρ ⊆ ⋃ i ∈ (Finset.univ : Finset ι), V i := by
    intro x hx
    obtain ⟨w, hw, hxw⟩ := hcov x hx
    exact mem_iUnion₂.2 ⟨⟨w, hw⟩, Finset.mem_univ _, (hVball ⟨w, hw⟩).1 (mem_ball.2 hxw)⟩
  
  let 𝒞 : Finset (Finset ι) := (Finset.univ : Finset (Finset ι)).filter
    fun I => sphere y ρ ⊆ ⋃ i ∈ I, V i
  have h𝒞 : 𝒞.Nonempty := ⟨Finset.univ, Finset.mem_filter.2 ⟨Finset.mem_univ _, hScov⟩⟩
  obtain ⟨I, hI𝒞, hImin⟩ := Finset.exists_min_image 𝒞 Finset.card h𝒞
  have hIcov : sphere y ρ ⊆ ⋃ i ∈ I, V i := (Finset.mem_filter.1 hI𝒞).2
  have hmin : ∀ i ∈ I, ¬ sphere y ρ ⊆ ⋃ j ∈ I.erase i, V j := by
    intro i hi hsub
    have hmem : I.erase i ∈ 𝒞 := Finset.mem_filter.2 ⟨Finset.mem_univ _, hsub⟩
    have := hImin _ hmem
    rw [Finset.card_erase_of_mem hi] at this
    have hpos : 0 < I.card := Finset.card_pos.2 ⟨i, hi⟩
    omega
  have hIne : I.Nonempty := by
    obtain ⟨i, hi, -⟩ := mem_iUnion₂.1 (hIcov (show y + (ρ : ℂ) ∈ sphere y ρ by
      rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_of_nonneg hρ.le]))
    exact ⟨i, hi⟩
  obtain ⟨i₀, hi₀⟩ := hIne
  
  have hpre : IsPreconnected (⋃ i ∈ I, T i) :=
    Objects.CorrectedEventContact.isPreconnected_biUnion_of_minimal_cover I T (fun i => (i : ℂ)) hTc hTp hTn hVb
      (isConnected_sphere (by
        rw [Complex.rank_real_complex]
        norm_num) y hρ.le).isPreconnected hIcov hmin
  have hgraph := reflTransGen_of_isPreconnected I T (fun i _ => hTc i) (fun i _ => hTn i) hpre hi₀
  
  obtain ⟨Tr, s, u, hTr, hTrt, hTrl⟩ := exists_curve_tour D I hi₀ (fun i => P i)
    (fun i => a i) (fun i => b i) (fun i _ => hP i i.2) hgraph
  have hTrA : Tr '' Icc s u ⊆ Objects.CorrectedEvent.ann y ρ₁ ρ₂ := by
    rw [hTrt]
    intro x hx
    obtain ⟨i, -, hxi⟩ := mem_iUnion₂.1 hx
    have hxa := hPA i i.2 hxi
    exact hin i i.2 (mem_closedBall.2 (le_of_lt hxa.2))
  have hTrD : LQGMetric.Disconnects (Tr '' Icc s u) (sphere y ρ₁) (sphere y ρ₂) := by
    intro x z γ hx hz
    have hS := path_meets_sphere γ (mem_sphere.1 hx) (mem_sphere.1 hz) h₁.le h₂.le
    have hxV : ∀ i ∈ I, x ∉ V i := by
      intro i _ hxV
      have hxb := (hVball i).2 hxV
      have hxann := hin i i.2 (mem_closedBall.2 (le_of_lt (mem_ball.1 hxb)))
      have hxy : dist x y = ρ₁ := mem_sphere.1 hx
      exact lt_irrefl _ (hxy ▸ hxann.1)
    have := Objects.CorrectedEventSeparator.path_meets_union_of_cover I T (fun i => (i : ℂ)) hTc hIcov γ hS hxV
    rw [hTrt]
    exact this
  calc Objects.CorrectedEvent.around D y ρ₁ ρ₂ ≤ D.len Tr s u :=
        iInf_le_of_le Tr (iInf_le_of_le s (iInf_le_of_le u (iInf_le_of_le hTr
          (iInf_le_of_le hTrA (iInf_le_of_le hTrD le_rfl)))))
    _ ≤ 2 * ∑ i ∈ I, D.len (P i) (a i) (b i) := hTrl
    _ ≤ 2 * ∑ w ∈ W, D.len (P w) (a w) (b w) := by
        gcongr
        calc ∑ i ∈ I, D.len (P i) (a i) (b i)
            ≤ ∑ i : ι, D.len (P i) (a i) (b i) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
                (fun _ _ _ => bot_le)
          _ = ∑ w ∈ W, D.len (P w) (a w) (b w) :=
              Finset.sum_coe_sort W (fun w => D.len (P w) (a w) (b w))

end SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails
