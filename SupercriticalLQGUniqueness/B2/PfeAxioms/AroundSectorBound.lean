import SupercriticalLQGUniqueness.B2.Strong.AroundFinite

 


set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open SupercriticalLQGUniqueness.B2.Strong

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem exists_curve_of_internalSetDist_lt
    (D : LSCMetric) (U : Set ℂ) (K₁ K₂ : Set ℂ) (M : ℝ≥0∞)
    (h : D.internalSetDist U (Subtype.val ⁻¹' K₁) (Subtype.val ⁻¹' K₂) < M) :
    ∃ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b ∧
      (∀ t ∈ Icc a b, P t ∈ U) ∧ P a ∈ K₁ ∧ P b ∈ K₂ ∧
      D.len P a b < M := by
  unfold LSCMetric.internalSetDist at h
  simp only [iInf_lt_iff] at h
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  unfold LSCMetric.internal at hxy
  simp only [iInf_lt_iff] at hxy
  obtain ⟨P, a, b, hP, hPU, hPa, hPb, hlen⟩ := hxy
  exact ⟨P, a, b, hP, hPU, hPa ▸ hx, hPb ▸ hy, hlen⟩

 

theorem aroundDist_lt_four_sector_bound
    (D : LSCMetric) (A : EuclideanAnnulus) (M : ℝ≥0∞)
    (h : ∀ k : Fin 4, D.internalSetDist (cfgOpens A k : Set ℂ)
      (Subtype.val ⁻¹' cfgSet₁ A k) (Subtype.val ⁻¹' cfgSet₂ A k) < M) :
    aroundDist D A < M + M + M + M := by
  choose P a b hP hU ha hb hlen using fun k =>
    exists_curve_of_internalSetDist_lt D _ _ _ M (h k)
  obtain ⟨s₀, hs₀, s₀', hs₀', s₁, hs₁, s₁', hs₁', s₂, hs₂, s₂', hs₂', s₃, hs₃, s₃', hs₃',
      z₁, z₂, z₃, hdisc⟩ := exists_around_loop A.center (annΔ_pos A)
    (pathIn_of_curve D A 0 (hP 0) (hU 0) (ha 0) (hb 0))
    (pathIn_of_curve D A 1 (hP 1) (hU 1) (ha 1) (hb 1))
    (pathIn_of_curve D A 2 (hP 2) (hU 2) (ha 2) (hb 2))
    (pathIn_of_curve D A 3 (hP 3) (hU 3) (ha 3) (hb 3))
  set Q := glue4 (seg (P 0) s₀ s₀') (seg (P 1) s₁ s₁')
    (seg (P 2) s₂ s₂') (seg (P 3) s₃ s₃')
  have hQpt : D.pt ∘ Q = glue4 (seg (D.pt ∘ P 0) s₀ s₀')
      (seg (D.pt ∘ P 1) s₁ s₁') (seg (D.pt ∘ P 2) s₂ s₂')
      (seg (D.pt ∘ P 3) s₃ s₃') := by
    funext t
    simp only [Function.comp, Q, glue4, seg]
    split_ifs <;> rfl
  have hcurve : D.IsCurve Q 0 4 := by
    refine ⟨by norm_num, ?_⟩
    rw [hQpt]
    exact continuousOn_glue4 _ _ _ _
      (continuousOn_seg (hP 0).2 hs₀ hs₀')
      (continuousOn_seg (hP 1).2 hs₁ hs₁')
      (continuousOn_seg (hP 2).2 hs₂ hs₂')
      (continuousOn_seg (hP 3).2 hs₃ hs₃')
      (by simp only [seg_one, seg_zero, Function.comp]; rw [z₁])
      (by simp only [seg_one, seg_zero, Function.comp]; rw [z₂])
      (by simp only [seg_one, seg_zero, Function.comp]; rw [z₃])
  have hlenQ : D.len Q 0 4 < M + M + M + M := by
    have e : D.len Q 0 4 = eVariationOn (D.pt ∘ Q) (Icc 0 4) := rfl
    rw [e, hQpt, eVariationOn_glue4 _ _ _ _
      (by simp only [seg_one, seg_zero, Function.comp]; rw [z₁])
      (by simp only [seg_one, seg_zero, Function.comp]; rw [z₂])
      (by simp only [seg_one, seg_zero, Function.comp]; rw [z₃])]
    have hseg := fun (k : Fin 4) (s s' : ℝ)
        (hs : s ∈ Icc (a k) (b k)) (hs' : s' ∈ Icc (a k) (b k)) =>
      (eVariationOn_seg_le (D.pt ∘ P k) hs hs').trans_lt (hlen k)
    gcongr
    · exact hseg 0 _ _ hs₀ hs₀'
    · exact hseg 1 _ _ hs₁ hs₁'
    · exact hseg 2 _ _ hs₂ hs₂'
    · exact hseg 3 _ _ hs₃ hs₃'
  have hinA : ∀ t ∈ Icc (0 : ℝ) 4, Q t ∈ A.toSet :=
    mapsTo_glue4 _ _ _ _
      (mapsTo_seg (fun t ht => cfgOpens_subset_toSet A 0 (hU 0 t ht)) hs₀ hs₀')
      (mapsTo_seg (fun t ht => cfgOpens_subset_toSet A 1 (hU 1 t ht)) hs₁ hs₁')
      (mapsTo_seg (fun t ht => cfgOpens_subset_toSet A 2 (hU 2 t ht)) hs₂ hs₂')
      (mapsTo_seg (fun t ht => cfgOpens_subset_toSet A 3 (hU 3 t ht)) hs₃ hs₃')
  have hdisc' : Disconnects (Q '' Icc 0 4) A.innerBoundary A.outerBoundary := by
    rw [disconnects_iff_lqgMetric_disconnects hcurve.isClosed_image]
    rw [exp_annL, exp_annL_add] at hdisc
    exact hdisc
  unfold aroundDist
  exact lt_of_le_of_lt
    (iInf_le_of_le Q (iInf_le_of_le 0 (iInf_le_of_le 4 (iInf_le_of_le hcurve
      (iInf_le_of_le hinA (iInf_le_of_le hdisc' le_rfl)))))) hlenQ

end SupercriticalLQGUniqueness.B2.PfeAxioms
