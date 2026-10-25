import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.OldGeoLenV2




 










set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Finset Filter LQGMetric.MetricGeometry
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices

open LQGMetric (DistC TestC)

 
theorem excursion_congr {P P' : ℝ → ℂ} {T : ℝ} {O : Set ℂ} {V : TopologicalSpace.Opens ℂ}
    {τ' τ σ σ' : ℝ} (hEq : Set.EqOn P' P (Icc 0 T))
    (he : EndSaving.Interfaces.Excursion P' T O V τ' τ σ σ') : EndSaving.Interfaces.Excursion P T O V τ' τ σ σ' := by
  obtain ⟨h0, h12, h23, h34, h4T, hf1, hf4, hin, hτ, hσ, hb, ha⟩ := he
  have hI : ∀ t, τ' ≤ t → t ≤ σ' → t ∈ Icc 0 T := fun t h1 h2 => ⟨h0.trans h1, h2.trans h4T⟩
  refine ⟨h0, h12, h23, h34, h4T, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hEq (hI τ' le_rfl (h12.trans (h23.trans h34)))]; exact hf1
  · rw [← hEq (hI σ' ((h12.trans h23).trans h34) le_rfl)]; exact hf4
  · intro t ht; rw [← hEq (hI t ht.1.le ht.2.le)]; exact hin t ht
  · rw [← hEq (hI τ h12 (h23.trans h34))]; exact hτ
  · rw [← hEq (hI σ (h12.trans h23) h34)]; exact hσ
  · intro t ht
    rw [← hEq (hI t ht.1.le (ht.2.le.trans (h23.trans h34)))]
    exact hb t ht
  · intro t ht
    rw [← hEq (hI t ((h12.trans h23).trans ht.1.le) ht.2.le)]
    exact ha t ht

 
theorem addFun_addFun_neg (g : DistC) (f : C(ℂ, ℝ)) :
    LQGMetric.addFun (LQGMetric.addFun g f) (-f) = g := by
  rw [addFun_addFun, add_neg_cancel, addFun_zero]

 
theorem object_f_zero_sphere {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} {h : Ω → DistC} {D D' : DistC → LSCMetric}
    {ξ : Set.Ioi (0 : ℝ)} {Q cMid : ℝ} {par : EndSaving.Interfaces.Parameters ξ} {pbar : Set.Ioo (0 : ℝ) 1}
    {z : ℂ} {r : Set.Ioi (0 : ℝ)}
    (obj : EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar z r) :
    ∀ x ∈ sphere z (r : ℝ), LQGMetric.testCont obj.f x = 0 := by
  intro x hx
  rw [testCont_apply]
  apply obj.f_off_V
  intro hxV
  have := (obj.V_annular.1 hxV).1
  rw [mem_sphere.mp hx] at this
  exact lt_irrefl _ this

 
theorem goodSite_shortcut {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (i : ℤ × ℤ) (g₀ : DistC)
    (hgood : EndSaving.FiniteEvents.GoodSiteV2 μ h D D' ξ Q cMid par pbar r b q K₁ K₂ obj i g₀)
    (P : ℝ → ℂ) (T : ℝ) (hU : EndSaving.FiniteEvents.UniqueSetGeodesic (D g₀) K₁ K₂ P T)
    (hP0 : P 0 ∉ ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (4 * (r : ℝ)))
    (hPT : P T ∉ ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (4 * (r : ℝ))) :
    ∃ hbr hrz s t : ℝ, IsCircleAverage g₀ b 0 hbr ∧
      IsCircleAverage g₀ r (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) hrz ∧
      EndSaving.FiniteEvents.LocalSizeBin ξ Q r b q hrz hbr ∧ 0 ≤ s ∧ s < t ∧ t ≤ T ∧
      (∀ u ∈ Icc s t, P u ∈ ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (4 * (r : ℝ))) ∧
      par.Cinc * scaleN ξ Q r hrz ≤ t - s ∧
      ∃ (hs : P s ∈ ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (4 * (r : ℝ)))
        (ht : P t ∈ ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (4 * (r : ℝ))),
        (D' g₀).internal (ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (4 * (r : ℝ)))
          (⟨P s, hs⟩, ⟨P t, ht⟩) ≤ ENNReal.ofReal (cMid * (t - s)) := by
  set z := LQGMetric.GM.gridPt ((r : ℝ) / 100) i with hz
  set W := ball z (4 * (r : ℝ)) with hW
  obtain ⟨hEplus, hbr, hrz, hbrc, hrzc, hbin, P', T', hU', τ', τ, σ, σ', hexc', hτ', hσ', hint⟩ :=
    hgood
  obtain ⟨hTT, hEq⟩ := hU.2 P' T' hU'.1
  subst hTT
  have hexc : EndSaving.Interfaces.Excursion P T' W (obj i).V τ' τ σ σ' := excursion_congr hEq hexc'
  set gplus := LQGMetric.addFun g₀ (LQGMetric.testCont (obj i).f) with hgplus
  have hcplus : IsCircleAverage gplus r z hrz :=
    isCircleAverage_addFun_of_zero_sphere g₀ _ r z hrz hrzc (object_f_zero_sphere (obj i))
  have hES := (obj i).E_shortcut gplus hEplus hrz hcplus
  simp only [hgplus, addFun_addFun_neg] at hES
  have hr0 : (0 : ℝ) < r := r.property
  have hO : IsOpen W := isOpen_ball
  have hVO : closure (((obj i).V : Set ℂ)) ⊆ W := by
    intro x hx
    have := ((obj i).closure_V_annulus hx).2
    rw [hW, mem_ball]; linarith
  have hexcS : (τ', τ, σ, σ') ∈ excSet P T' W (obj i).V := hexc
  obtain ⟨he12, he34, _, _⟩ := exc_basic hO hVO hexcS
  obtain ⟨hτ₂, hσ₂, himp⟩ := hES P T' τ' τ σ σ' hU.1.1 hP0 hPT hexc
  have hPτ : P' τ = P τ := hEq ⟨hexc.1.trans hexc.2.1, hexc.2.2.1.trans (hexc.2.2.2.1.trans hexc.2.2.2.2.1)⟩
  have hPσ : P' σ = P σ := hEq ⟨(hexc.1.trans hexc.2.1).trans hexc.2.2.1, hexc.2.2.2.1.trans hexc.2.2.2.2.1⟩
  have hint' : ENNReal.ofReal par.Ctime * ENNReal.ofReal ((r : ℝ) ^ ((ξ : ℝ) * Q) *
      Real.exp ((ξ : ℝ) * hrz)) ≤ (D gplus).internal W (⟨P τ, hτ₂⟩, ⟨P σ, hσ₂⟩) := by
    have heq : (⟨P' τ, hτ'⟩ : W) = ⟨P τ, hτ₂⟩ := Subtype.ext hPτ
    have heq' : (⟨P' σ, hσ'⟩ : W) = ⟨P σ, hσ₂⟩ := Subtype.ext hPσ
    rw [← heq, ← heq']
    exact hint
  obtain ⟨s, t, hτs, hst, htσ, hCinc, hs, ht, hshort⟩ := himp hint'
  refine ⟨hbr, hrz, s, t, hbrc, hrzc, hbin, hexc.1.trans (hexc.2.1.trans hτs), hst,
    htσ.trans (hexc.2.2.2.1.trans hexc.2.2.2.2.1), ?_, ?_, hs, ht, hshort⟩
  · intro u hu
    exact hexc.2.2.2.2.2.2.2.1 u ⟨he12.trans_le (hτs.trans hu.1), hu.2.trans_lt (htσ.trans_lt he34)⟩
  · have hN := scaleN_pos ξ Q r hrz
    rw [← ENNReal.ofReal_mul par.inc_pos.le] at hCinc
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp hCinc


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices
