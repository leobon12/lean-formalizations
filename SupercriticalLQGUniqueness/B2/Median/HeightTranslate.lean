import SupercriticalLQGUniqueness.B2.Median.Height
import SupercriticalLQGUniqueness.B2.Median.Scale

 





set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Median

private theorem image_upper_half_inter (V : Set ℂ) (z : ℂ) (s : ℝ) :
    (fun w : ℂ => w + z) '' (V ∩ {w | s ≤ w.im}) =
      ((fun w : ℂ => w + z) '' V) ∩ {w | s + z.im ≤ w.im} := by
  ext w
  constructor
  · rintro ⟨v, ⟨hv, hvs⟩, rfl⟩
    refine ⟨⟨v, hv, rfl⟩, ?_⟩
    change s ≤ v.im at hvs
    change s + z.im ≤ (v + z).im
    rw [Complex.add_im]
    linarith
  · rintro ⟨⟨v, hv, rfl⟩, hvs⟩
    refine ⟨v, ⟨hv, ?_⟩, rfl⟩
    change s ≤ v.im
    change s + z.im ≤ (v + z).im at hvs
    rw [Complex.add_im] at hvs
    linarith

private theorem image_lower_half_inter (V : Set ℂ) (z : ℂ) (s : ℝ) :
    (fun w : ℂ => w + z) '' (V ∩ {w | w.im ≤ s}) =
      ((fun w : ℂ => w + z) '' V) ∩ {w | w.im ≤ s + z.im} := by
  ext w
  constructor
  · rintro ⟨v, ⟨hv, hvs⟩, rfl⟩
    refine ⟨⟨v, hv, rfl⟩, ?_⟩
    change v.im ≤ s at hvs
    change (v + z).im ≤ s + z.im
    rw [Complex.add_im]
    linarith
  · rintro ⟨⟨v, hv, rfl⟩, hvs⟩
    refine ⟨v, ⟨hv, ?_⟩, rfl⟩
    change v.im ≤ s
    change (v + z).im ≤ s + z.im at hvs
    rw [Complex.add_im] at hvs
    linarith

theorem upperPathInf_translate (D E : LSCMetric) (z : ℂ)
    (hDE : ∀ x y : ℂ, E (x, y) = D (x + z, y + z))
    (V A B : Set ℂ) (s : ℝ) :
    upperPathInf E V A B s =
      upperPathInf D ((fun w : ℂ => w + z) '' V)
        ((fun w : ℂ => w + z) '' A) ((fun w : ℂ => w + z) '' B)
        (s + z.im) := by
  unfold upperPathInf
  rw [compactPathInf_translate D E z hDE]
  congr 1 <;> exact image_upper_half_inter _ z s

theorem lowerPathInf_translate (D E : LSCMetric) (z : ℂ)
    (hDE : ∀ x y : ℂ, E (x, y) = D (x + z, y + z))
    (V A B : Set ℂ) (s : ℝ) :
    lowerPathInf E V A B s =
      lowerPathInf D ((fun w : ℂ => w + z) '' V)
        ((fun w : ℂ => w + z) '' A) ((fun w : ℂ => w + z) '' B)
        (s + z.im) := by
  unfold lowerPathInf
  rw [compactPathInf_translate D E z hDE]
  congr 1 <;> exact image_lower_half_inter _ z s

end SupercriticalLQGUniqueness.B2.Median
