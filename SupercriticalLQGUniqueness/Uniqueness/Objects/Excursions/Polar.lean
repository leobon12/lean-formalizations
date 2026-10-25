import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Object
import SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent.EventPredicate




 













set_option autoImplicit false

noncomputable section

open Set Metric Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions

open SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

theorem polar_eq_pol (s θ : ℝ) : Objects.CorrectedEvent.polar s θ = pol s θ := rfl

 
theorem image_lerp_Icc (a b : ℝ) : (fun t : ℝ => a + t * (b - a)) '' Icc 0 1 = uIcc a b := by
  have h := segment_eq_image' ℝ a b
  rw [segment_eq_uIcc] at h
  rw [h]
  rfl

theorem range_polarPath_eq (R₁ R₂ φ₁ φ₂ : ℝ) :
    range (polarPath R₁ R₂ φ₁ φ₂) =
      (fun t : ℝ => pol (R₁ + t * (R₂ - R₁)) (φ₁ + t * (φ₂ - φ₁))) '' Icc 0 1 := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, ⟨t.2.1, t.2.2⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩

 
theorem range_spoke (R₁ R₂ φ : ℝ) :
    range (polarPath R₁ R₂ φ φ) = (fun R => pol R φ) '' uIcc R₁ R₂ := by
  rw [range_polarPath_eq, ← image_lerp_Icc, image_image]
  congr 1
  funext t
  simp

 
theorem range_arc (R φ₁ φ₂ : ℝ) :
    range (polarPath R R φ₁ φ₂) = (fun θ => pol R θ) '' uIcc φ₁ φ₂ := by
  rw [range_polarPath_eq, ← image_lerp_Icc, image_image]
  congr 1
  funext t
  simp

 
theorem seg76_eq (a b : ℂ) : Objects.CorrectedEvent.segment a b = segment ℝ a b := by
  rw [segment_eq_image]
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, by simp [Complex.real_smul]⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, by simp [Complex.real_smul]⟩

 
theorem arc76_eq (s θ0 θ1 : ℝ) : Objects.CorrectedEvent.arc s θ0 θ1 = (fun θ => pol s θ) '' uIcc θ0 θ1 := by
  ext z
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    exact ⟨θ, by rw [uIcc]; exact hθ, rfl⟩
  · rintro ⟨θ, hθ, rfl⟩
    exact ⟨θ, by rw [uIcc] at hθ; exact hθ, rfl⟩

 
theorem radial76_eq (a b ψ : ℝ) :
    {w : ℂ | ∃ t ∈ Icc a b, w = Objects.CorrectedEvent.polar t ψ} = (fun R => pol R ψ) '' Icc a b := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩

 
theorem segment_zero_pol {a ψ : ℝ} (ha : 0 ≤ a) :
    segment ℝ (0 : ℂ) (pol a ψ) = (fun R => pol R ψ) '' Icc 0 a := by
  rw [segment_eq_image']
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t * a, ⟨mul_nonneg ht.1 ha, by nlinarith [ht.2]⟩, ?_⟩
    simp [pol, Complex.real_smul]
    ring
  · rintro ⟨R, hR, rfl⟩
    rcases eq_or_lt_of_le ha with h | h
    · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      have : R = 0 := le_antisymm (h ▸ hR.2) hR.1
      simp [pol, this]
    · refine ⟨R / a, ⟨div_nonneg hR.1 ha, (div_le_one h).mpr hR.2⟩, ?_⟩
      have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast h.ne'
      simp only [pol, zero_add, sub_zero, Complex.real_smul]
      push_cast
      field_simp

 
theorem segment_real_pos {a b : ℝ} (hab : a ≤ b) :
    segment ℝ (a : ℂ) (b : ℂ) = (fun R => pol R 0) '' Icc a b := by
  have h := segment_eq_image' ℝ (a : ℂ) (b : ℂ)
  have himg : segment ℝ a b = Icc a b := by rw [segment_eq_uIcc, uIcc_of_le hab]
  rw [← himg, segment_eq_image' ℝ a b, h, image_image]
  congr 1
  funext t
  simp [pol, ex, Complex.real_smul]

 
theorem segment_neg_zero {c : ℝ} (hc : 0 ≤ c) :
    segment ℝ (-(c : ℂ)) (0 : ℂ) = (fun R => pol R π) '' Icc 0 c := by
  rw [segment_eq_image']
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(1 - t) * c, ⟨mul_nonneg (by linarith [ht.2]) hc, by nlinarith [ht.1]⟩, ?_⟩
    dsimp only
    rw [pol_pi]
    simp [Complex.real_smul]
    ring
  · rintro ⟨R, hR, rfl⟩
    dsimp only
    rw [pol_pi]
    rcases eq_or_lt_of_le hc with h | h
    · have : R = 0 := le_antisymm (h ▸ hR.2) hR.1
      refine ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
      simp [this, ← h]
    · refine ⟨1 - R / c, ⟨by rw [sub_nonneg]; exact (div_le_one h).mpr hR.2,
        by linarith [div_nonneg hR.1 h.le]⟩, ?_⟩
      have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast h.ne'
      simp only [sub_neg_eq_add, zero_add, Complex.real_smul]
      push_cast
      field_simp
      ring

end SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions
