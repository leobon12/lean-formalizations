/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedCloseCoords

/-!
# Entrance integrability and continuity of the mapped noise

Packet PROVE-ZHAN-GT4-A22. The D10 rate need not be continuous at a seed
entrance. Its integrability suffices for continuity of its primitive and
of the spliced own-time noise, including at the stopping horizon.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

/-- The finite image gap integrals make the actual D10 rate integrable. -/
theorem SeedData.intervalIntegrable_d10Rate {n : ℕ} (s : SeedData n) {t : ℝ}
    (hi : ∀ i, IntervalIntegrable
      (fun u => s.A 1 u ^ 2 / (s.A 0 u - s.imageForce u i)) volume 0 t) :
    IntervalIntegrable s.d10Rate volume 0 t := by
  rw [show s.d10Rate = (fun u => ∑ i, s.A 1 u ^ 2 *
    (s.imageCharge i / (s.A 0 u - s.imageForce u i))) from
      funext s.d10Rate_eq_imageCharge]
  have hi' (i : Fin (n + 1)) : IntervalIntegrable (fun u =>
      s.A 1 u ^ 2 * (s.imageCharge i / (s.A 0 u - s.imageForce u i))) volume 0 t := by
    convert (hi i).const_mul (s.imageCharge i) using 1
    funext u
    ring
  exact ⟨integrable_finsetSum _ (fun i _ => (hi' i).1),
    integrable_finsetSum _ (fun i _ => (hi' i).2)⟩

/-- Continuity of the D10 primitive requires only its entrance integral. -/
theorem SeedData.continuousOn_integral_d10Rate {n : ℕ} (s : SeedData n) {T : ℝ}
    (hT : 0 ≤ T)
    (hi : ∀ i, IntervalIntegrable
      (fun u => s.A 1 u ^ 2 / (s.A 0 u - s.imageForce u i)) volume 0 T) :
    ContinuousOn (fun t => ∫ u in (0 : ℝ)..t, s.d10Rate u) (Icc 0 T) := by
  have hI : IntegrableOn s.d10Rate (uIcc 0 T) := by
    rw [uIcc_of_le hT]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT).1 (s.intervalIntegrable_d10Rate hi)
  have hh := intervalIntegral.continuousOn_primitive_interval
    (a := 0) (b := T) (μ := volume) (f := s.d10Rate) hI
  simpa only [uIcc_of_le hT] using hh

/-- The actual spliced mapped noise is continuous, so its continuity is
not an additional stochastic D10 input. -/
theorem continuous_seedOwnMappedNoise {Ω : Type*} {n : ℕ} {κ : ℝ}
    {d : Ω → SeedData n} {S : Ω → ℝ≥0} {A : Ω → Set ℂ} {B : ℝ≥0 → Ω → ℝ}
    (hown : ∀ ω, OwnData (d ω).W (A ω) (d ω).φ (S ω) (d ω).a (d ω).W')
    (hB : ∀ ω, Continuous (B · ω))
    (hi : ∀ ω i, IntervalIntegrable
      (fun u => (d ω).A 1 u ^ 2 / ((d ω).A 0 u - (d ω).imageForce u i)) volume 0 (S ω))
    (ω : Ω) : Continuous (seedOwnMappedNoise κ d S B · ω) := by
  have ht : Continuous (fun u : ℝ≥0 => ((min u (S ω) : ℝ≥0) : ℝ)) :=
    NNReal.continuous_coe.comp (continuous_id.min continuous_const)
  have hm : ∀ u : ℝ≥0, ((min u (S ω) : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) (S ω) :=
    fun u => ⟨(min u (S ω)).coe_nonneg, min_le_right _ _⟩
  have hA := ((hown ω).continuousOn_frzA 0).comp_continuous ht hm
  have hJ := ((d ω).continuousOn_integral_d10Rate (S ω).coe_nonneg (hi ω)).comp_continuous ht hm
  exact (((hA.sub continuous_const).sub hJ).div_const _).add
    ((hB ω).sub ((hB ω).comp (continuous_id.min continuous_const)))

end InteractingSLE.ZhanGT4
