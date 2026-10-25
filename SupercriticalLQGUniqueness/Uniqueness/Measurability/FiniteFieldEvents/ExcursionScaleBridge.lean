import SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents.ExcursionCongr
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling.ExcursionScale




 
set_option autoImplicit false
noncomputable section
open Set unitInterval
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents

def normalizedExcursionTimes (T a b c d : ℝ) : Fin 5 → ℝ :=
  ![1, a / T, b / T, c / T, d / T]

private theorem scaled_source_eq_unitExtension
    (P : ℝ → ℂ) (T : ℝ) (R : Measurability.GeodesicCodes.Path) (hT : 0 < T)
    (hscaled : ∀ q : unitInterval, R q = P (T * (q : ℝ))) :
    Set.EqOn (P ∘ fun t => t / (1 / T)) (unitExtension R) (Icc 0 1) := by
  intro t ht
  have hproj : ((projIcc 0 1 zero_le_one t : unitInterval) : ℝ) = t :=
    congrArg Subtype.val (projIcc_of_mem zero_le_one ht)
  change P (t / (1 / T)) = R (projIcc 0 1 zero_le_one t)
  rw [hscaled, hproj]
  congr 1
  field_simp

theorem scaled_unitExtension_eq_source
    (P : ℝ → ℂ) (T : ℝ) (R : Measurability.GeodesicCodes.Path) (hT : 0 < T)
    (hscaled : ∀ q : unitInterval, R q = P (T * (q : ℝ))) :
    Set.EqOn ((unitExtension R) ∘ fun t => t / T) P (Icc 0 T) := by
  intro t ht
  have ht' : t / T ∈ Icc 0 1 := by
    constructor
    · exact div_nonneg ht.1 hT.le
    · exact (div_le_one hT).2 ht.2
  have hproj : ((projIcc 0 1 zero_le_one (t / T) : unitInterval) : ℝ) = t / T :=
    congrArg Subtype.val (projIcc_of_mem zero_le_one ht')
  change R (projIcc 0 1 zero_le_one (t / T)) = P t
  rw [hscaled, hproj]
  congr 1
  field_simp

theorem excursion_iff_unitExcursion_of_scaled
    (P : ℝ → ℂ) (T : ℝ) (R : Measurability.GeodesicCodes.Path) (hT : 0 < T)
    (hscaled : ∀ q : unitInterval, R q = P (T * (q : ℝ)))
    (O : Set ℂ) (V : TopologicalSpace.Opens ℂ)
    (a b c d : ℝ) :
    EndSaving.Interfaces.Excursion P T O V a b c d ↔
      UnitExcursion O V (R, normalizedExcursionTimes T a b c d) := by
  have hinv : 0 < 1 / T := one_div_pos.mpr hT
  constructor
  · intro hex
    have hres := EndSaving.Scaling.excursion_rescale P T O V a b c d (1 / T) hinv hex
    have hcongr := (excursion_congr_on (P ∘ fun t => t / (1 / T))
      (unitExtension R) 1 O V ((1 / T) * a) ((1 / T) * b)
      ((1 / T) * c) ((1 / T) * d)
      (scaled_source_eq_unitExtension P T R hT hscaled)).1
    have hmul : (1 / T) * T = 1 := by field_simp
    rw [hmul] at hres
    have hmain := hcongr hres
    have hn : EndSaving.Interfaces.Excursion (unitExtension R) 1 O V
        (a / T) (b / T) (c / T) (d / T) := by
      simpa only [one_div, inv_mul_eq_div] using hmain
    change (1 : ℝ) = 1 ∧
      EndSaving.Interfaces.Excursion (unitExtension R) 1 O V
        (a / T) (b / T) (c / T) (d / T)
    exact ⟨rfl, hn⟩
  · intro hex
    have hcode : EndSaving.Interfaces.Excursion (unitExtension R) 1 O V
        (a / T) (b / T) (c / T) (d / T) := by
      exact hex.2
    have hres := EndSaving.Scaling.excursion_rescale (unitExtension R) 1 O V
      (a / T) (b / T) (c / T) (d / T) T hT hcode
    have hcongr := (excursion_congr_on
      ((unitExtension R) ∘ fun t => t / T) P T O V
      (T * (a / T)) (T * (b / T)) (T * (c / T)) (T * (d / T))
      (scaled_unitExtension_eq_source P T R hT hscaled)).1
    have hmain := hcongr (by simpa only [mul_one] using hres)
    have htime (s : ℝ) : T * (s / T) = s := by field_simp
    simpa only [mul_one, htime] using hmain

end SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents
