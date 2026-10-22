import HigherDimLQGMetric.Sharp.W3Params

/-! Conversion of a two-parameter tail to one sharp polynomial tail. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory
open scoped ENNReal

theorem w3_combine_tail {ξ p a' θ a T B J C₀ : ℝ}
    (hξ : 0 < ξ) (_hp : 0 < p) (_ha' : 0 < a')
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hθp : a < θ * p) (hγa : a < (1 - θ) * a' / ξ)
    (hT : 0 < T) (hB : 0 ≤ B) (hJ : 0 ≤ J) (hC₀ : 1 ≤ C₀) :
    ∃ Ctail t₀ : ℝ, 1 ≤ t₀ ∧ 0 ≤ Ctail ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (X : Ω → ℝ≥0∞),
      (∀ A : ℝ, 1 ≤ A → ∀ C : ℝ, C₀ ≤ C →
        P {ω | ENNReal.ofReal (T * A * C ^ ξ) < X ω} ≤
          ENNReal.ofReal (B * A ^ (-p)) + ENNReal.ofReal (J * C ^ (-a'))) →
      ∀ t : ℝ, t₀ ≤ t →
        P {ω | ENNReal.ofReal t < X ω} ≤ ENNReal.ofReal (Ctail * t ^ (-a)) := by
  let γ : ℝ := (1 - θ) / ξ
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hγξ : γ * ξ = 1 - θ := by dsimp [γ]; field_simp
  have hγa' : a < γ * a' := by
    dsimp [γ]
    simpa only [div_mul_eq_mul_div] using hγa
  let t₀ : ℝ := max 1 (T * max 1 (C₀ ^ (1 / γ)))
  have ht₀ : 1 ≤ t₀ := le_max_left _ _
  let Ctail : ℝ := B * T ^ (θ * p) + J * T ^ (γ * a')
  have hCtail : 0 ≤ Ctail := by dsimp [Ctail]; positivity
  refine ⟨Ctail, t₀, ht₀, hCtail, ?_⟩
  intro Ω _ P _ X htwo t ht
  have ht1 : 1 ≤ t := ht₀.trans ht
  have htpos : 0 < t := by linarith
  let s : ℝ := t / T
  have hs : 0 < s := by dsimp [s]; positivity
  have hs1 : 1 ≤ s := by
    have hTbound : T ≤ t := by
      have hmax : (1 : ℝ) ≤ max 1 (C₀ ^ (1 / γ)) := le_max_left _ _
      have hm := mul_le_mul_of_nonneg_left hmax hT.le
      dsimp [t₀] at ht
      simpa only [mul_one] using (hm.trans (le_max_right _ _)).trans ht
    exact (le_div_iff₀ hT).2 (by simpa only [one_mul] using hTbound)
  have hsC : C₀ ^ (1 / γ) ≤ s := by
    have hm : T * C₀ ^ (1 / γ) ≤
        T * max 1 (C₀ ^ (1 / γ)) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hT.le
    have ht' : T * C₀ ^ (1 / γ) ≤ t :=
      hm.trans ((le_max_right _ _).trans ht)
    exact (le_div_iff₀ hT).2 (by simpa only [mul_comm] using ht')
  let A : ℝ := s ^ θ
  let C : ℝ := s ^ γ
  have hA : 1 ≤ A := Real.one_le_rpow hs1 hθ0.le
  have hC : C₀ ≤ C := by
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ C₀ ^ (1 / γ)) hsC hγ.le
    have he : (C₀ ^ (1 / γ)) ^ γ = C₀ := by
      rw [← Real.rpow_mul (by linarith : 0 ≤ C₀)]
      have hγne : γ ≠ 0 := hγ.ne'
      rw [show (1 / γ) * γ = 1 by field_simp, Real.rpow_one]
    simpa only [C, he] using hpow
  have hTA : T * A * C ^ ξ = t := by
    dsimp [A, C]
    rw [← Real.rpow_mul hs.le γ ξ]
    calc
      T * s ^ θ * s ^ (γ * ξ) = T * (s ^ θ * s ^ (γ * ξ)) := by ring
      _ = T * s ^ (θ + γ * ξ) := by rw [Real.rpow_add hs]
      _ = T * s := by rw [hγξ, show θ + (1 - θ) = 1 by ring, Real.rpow_one]
      _ = t := by dsimp [s]; field_simp
  have hbound := htwo A hA C hC
  rw [hTA] at hbound
  have hAp : A ^ (-p) = t ^ (-(θ * p)) * T ^ (θ * p) := by
    dsimp [A, s]
    rw [← Real.rpow_mul hs.le θ (-p)]
    have he : θ * -p = -(θ * p) := by ring
    rw [he, Real.div_rpow htpos.le hT.le]
    rw [Real.rpow_neg hT.le]
    field_simp
  have hCp : C ^ (-a') = t ^ (-(γ * a')) * T ^ (γ * a') := by
    dsimp [C, s]
    rw [← Real.rpow_mul hs.le γ (-a')]
    have he : γ * -a' = -(γ * a') := by ring
    rw [he, Real.div_rpow htpos.le hT.le]
    rw [Real.rpow_neg hT.le]
    field_simp
  have htp : t ^ (-(θ * p)) ≤ t ^ (-a) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (by linarith only [hθp])
  have hta : t ^ (-(γ * a')) ≤ t ^ (-a) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (by linarith only [hγa'])
  have hBpart : B * A ^ (-p) ≤ B * T ^ (θ * p) * t ^ (-a) := by
    rw [hAp]
    have hfac : 0 ≤ B * T ^ (θ * p) := by positivity
    have hm := mul_le_mul_of_nonneg_left htp hfac
    nlinarith only [hm]
  have hJpart : J * C ^ (-a') ≤ J * T ^ (γ * a') * t ^ (-a) := by
    rw [hCp]
    have hfac : 0 ≤ J * T ^ (γ * a') := by positivity
    have hm := mul_le_mul_of_nonneg_left hta hfac
    nlinarith only [hm]
  have hBnon : 0 ≤ B * A ^ (-p) := by positivity
  have hJnon : 0 ≤ J * C ^ (-a') := by positivity
  calc
    P {ω | ENNReal.ofReal t < X ω} ≤
        ENNReal.ofReal (B * A ^ (-p)) + ENNReal.ofReal (J * C ^ (-a')) := hbound
    _ = ENNReal.ofReal (B * A ^ (-p) + J * C ^ (-a')) := by
      rw [ENNReal.ofReal_add hBnon hJnon]
    _ ≤ ENNReal.ofReal (Ctail * t ^ (-a)) := by
      apply ENNReal.ofReal_le_ofReal
      dsimp [Ctail]
      nlinarith only [hBpart, hJpart]

end HigherDimLQGMetric
