import SupercriticalLQGUniqueness.Frozen.WeylScale




 
















set_option autoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProducerBlocks

open SupercriticalLQGUniqueness

 
theorem isCurve_of_le (D E : LSCMetric) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hle : ∀ x y : ℂ, E (x, y) ≤ C * D (x, y)) {P : ℝ → ℂ} {a b : ℝ}
    (h : D.IsCurve P a b) : E.IsCurve P a b := by
  refine ⟨h.1, ?_⟩
  have hL : LipschitzWith C.toNNReal (fun x : D.Space => (E.pt x : E.Space)) := by
    intro x y
    change E (x, y) ≤ (C.toNNReal : ℝ≥0∞) * D (x, y)
    rw [ENNReal.coe_toNNReal hC]
    exact hle x y
  exact hL.continuous.comp_continuousOn h.2

 
theorem len_le_of_le (D E : LSCMetric) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hle : ∀ x y : ℂ, E (x, y) ≤ C * D (x, y)) (P : ℝ → ℂ) (a b : ℝ) :
    E.len P a b ≤ C * D.len P a b := by
  have hL' : LipschitzWith C.toNNReal (fun x : D.Space => (E.pt x : E.Space)) := by
    intro x y
    change E (x, y) ≤ (C.toNNReal : ℝ≥0∞) * D (x, y)
    rw [ENNReal.coe_toNNReal hC]
    exact hle x y
  have hL : LipschitzOnWith C.toNNReal (fun x : D.Space => (E.pt x : E.Space)) univ :=
    hL'.lipschitzOnWith
  have := hL.comp_eVariationOn_le (g := D.pt ∘ P) (s := Icc a b) (mapsTo_univ _ _)
  rw [ENNReal.coe_toNNReal hC] at this
  exact this

 

theorem internal_le_of_curves (D E : LSCMetric) {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (Y : Set ℂ) (hcurve : ∀ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b → E.IsCurve P a b)
    (hlen : ∀ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b → E.len P a b ≤ C * D.len P a b)
    (p : Y × Y) : E.internal Y p ≤ C * D.internal Y p := by
  unfold LSCMetric.internal
  simp_rw [ENNReal.mul_iInf_of_ne hC0 hCtop]
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hD =>
    le_iInf fun hY => le_iInf fun h0 => le_iInf fun h1 => ?_
  exact iInf_le_of_le P (iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le (hcurve P a b hD)
    (iInf_le_of_le hY (iInf_le_of_le h0 (iInf_le_of_le h1 (hlen P a b hD)))))))

 

theorem internal_le_of_le (D E : LSCMetric) {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hle : ∀ x y : ℂ, E (x, y) ≤ C * D (x, y)) (Y : Set ℂ) (p : Y × Y) :
    E.internal Y p ≤ C * D.internal Y p :=
  internal_le_of_curves D E hC0 hCtop Y (fun _ _ _ h => isCurve_of_le D E hCtop hle h)
    (fun P a b _ => len_le_of_le D E hCtop hle P a b) p

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProducerBlocks

