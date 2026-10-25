import Mathlib




 

















set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.T58Numerics

 
theorem eloop_margin {r ε : ℝ} (hr : 0 < r) (hε0 : 0 < ε) (hε : ε < 1 / 4) {z : ℂ}
    (hz1 : 3 / 2 * r ≤ ‖z‖) (hz2 : ‖z‖ ≤ 5 / 2 * r) :
    (∀ x : ℂ, ‖x - z‖ ≤ Real.sqrt ε * r → r < ‖x‖ ∧ ‖x‖ < 4 * r) ∧
    (∀ x : ℂ, ‖x‖ = 3 * r → Real.sqrt ε * r < ‖x - z‖) ∧
    (∀ x : ℂ, ‖x‖ = 4 * r → Real.sqrt ε * r < ‖x - z‖) := by
  have hs : Real.sqrt ε < 1 / 2 := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt hε0.le hε
  have hsr : Real.sqrt ε * r < r / 2 := by nlinarith
  refine ⟨fun x hx => ⟨?_, ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · have := norm_sub_norm_le z x
    rw [norm_sub_rev] at hx
    linarith
  · have := norm_sub_norm_le x z
    linarith
  · have := norm_sub_norm_le x z
    linarith
  · have := norm_sub_norm_le x z
    linarith

 
theorem exists_Asp {θ Aac Aar Aep : ℝ} (hθ : 0 < θ) (hac : 0 < Aac) (har : 0 < Aar)
    (hep : 0 < Aep) :
    ∃ Asp : ℝ, 0 < Asp ∧ Asp < Aep ∧ 4 * Asp ^ θ * Aar < Aac ^ 2 / (16 * Aar) := by
  have hc : 0 < Aac ^ 2 / (16 * Aar) / (4 * Aar) := by positivity
  
  have ht : Filter.Tendsto (fun t : ℝ => t ^ θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have := (Real.continuousAt_rpow_const 0 θ (Or.inr hθ.le)).tendsto
    rw [Real.zero_rpow hθ.ne'] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ^ θ < Aac ^ 2 / (16 * Aar) / (4 * Aar) :=
    ht (Iio_mem_nhds hc)
  have hpos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Ioi (0 : ℝ) :=
    eventually_mem_nhdsWithin
  have hlt : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t < Aep :=
    nhdsWithin_le_nhds (Iio_mem_nhds hep)
  have hev2 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < t ∧ t < Aep :=
    hpos.and hlt
  obtain ⟨t, ht1, ht2, ht3⟩ := ((hev.and hev2).exists)
  refine ⟨t, ht2, ht3, ?_⟩
  have h4 : 0 < 4 * Aar := by positivity
  have := (lt_div_iff₀ h4).1 ht1
  linarith [mul_comm (t ^ θ) (4 * Aar)]

 

theorem sp_contradiction {Aac Aar N ℓseg ℓπ : ℝ} (hac : 0 < Aac) (har : 0 < Aar) (hN : 0 < N)
    (hseg : ℓseg < Aac ^ 2 / (16 * Aar) * N) (hπ : ℓπ < Aac ^ 2 / (16 * Aar) * N) :
    ℓseg + ℓπ < Aac ^ 2 / (4 * Aar) * N := by
  have : Aac ^ 2 / (16 * Aar) * N * 2 < Aac ^ 2 / (4 * Aar) * N := by
    have h1 : Aac ^ 2 / (4 * Aar) = 4 * (Aac ^ 2 / (16 * Aar)) := by field_simp; ring
    rw [h1]
    have : 0 < Aac ^ 2 / (16 * Aar) * N := by positivity
    nlinarith
  linarith

 
theorem holder_exponent {ξ Q p : ℝ} (hξ : 0 < ξ) (hp : 0 < p) (hpQ : p < 2 * Q / ξ) :
    ∃ q : ℝ, 1 < q ∧ 0 < ξ * Q * p - q * p ^ 2 * ξ ^ 2 / 2 := by
  have hgap : 0 < ξ * Q * p - p ^ 2 * ξ ^ 2 / 2 := by
    have h1 : p * ξ < 2 * Q := by rwa [lt_div_iff₀ hξ] at hpQ
    have : 0 < p * ξ * (2 * Q - p * ξ) := by
      have : 0 < p * ξ := by positivity
      nlinarith
    nlinarith
  set g := ξ * Q * p - p ^ 2 * ξ ^ 2 / 2 with hg
  have hb : 0 < p ^ 2 * ξ ^ 2 / 2 := by positivity
  refine ⟨1 + g / (2 * (p ^ 2 * ξ ^ 2 / 2)), ?_, ?_⟩
  · have : 0 < g / (2 * (p ^ 2 * ξ ^ 2 / 2)) := by positivity
    linarith
  · have e : (1 + g / (2 * (p ^ 2 * ξ ^ 2 / 2))) * p ^ 2 * ξ ^ 2 / 2 =
        p ^ 2 * ξ ^ 2 / 2 + g / 2 := by
      field_simp
    have e2 : ξ * Q * p - (1 + g / (2 * (p ^ 2 * ξ ^ 2 / 2))) * p ^ 2 * ξ ^ 2 / 2 = g / 2 := by
      rw [e, hg]; ring
    rw [e2]; positivity

 


theorem rate_of_moments {a δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → C * R ^ (-(a - δ / 2)) ≤ R ^ (-a + δ) := by
  refine ⟨max 1 (C ^ (2 / δ)), le_max_left _ _, fun R hR => ?_⟩
  have hR1 : 1 ≤ R := le_trans (le_max_left _ _) hR
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  have hCR : C ≤ R ^ (δ / 2) := by
    have h1 : C ^ (2 / δ) ≤ R := le_trans (le_max_right _ _) hR
    have h2 : (C ^ (2 / δ)) ^ (δ / 2) ≤ R ^ (δ / 2) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hC.le _) h1 (by positivity)
    rwa [← Real.rpow_mul hC.le, show 2 / δ * (δ / 2) = 1 by field_simp, Real.rpow_one] at h2
  calc C * R ^ (-(a - δ / 2)) ≤ R ^ (δ / 2) * R ^ (-(a - δ / 2)) :=
        mul_le_mul_of_nonneg_right hCR (Real.rpow_nonneg hR0.le _)
    _ = R ^ (-a + δ) := by
        rw [← Real.rpow_add hR0]; ring_nf

 
theorem markov_rpow {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {X : Ω → ℝ≥0∞}
    (hX : AEMeasurable X P) {p : ℝ} (hp : 0 < p) (R : ℝ≥0∞) :
    R ^ p * P {ω | R ≤ X ω} ≤ ∫⁻ ω, X ω ^ p ∂P := by
  have hm : AEMeasurable (fun ω => X ω ^ p) P := hX.pow_const p
  calc R ^ p * P {ω | R ≤ X ω} ≤ R ^ p * P {ω | R ^ p ≤ X ω ^ p} := by
        refine mul_le_mul' le_rfl (measure_mono ?_)
        intro ω hω
        exact ENNReal.rpow_le_rpow hω hp.le
    _ ≤ ∫⁻ ω, X ω ^ p ∂P := mul_meas_ge_le_lintegral₀ hm _

end SupercriticalLQGUniqueness.Uniqueness.Objects.T58Numerics

