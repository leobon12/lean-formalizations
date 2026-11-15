/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedR80Meas

/-!
# Positive-time continuity of the actual image drift

Packet PROVE-ZHAN-GT4-A22. Reflection across the protected seed-coordinate
interval gives continuity of the image forces. The rational D10 expression
is continuous at positive times, although its entrance value may be singular.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped NNReal
namespace InteractingSLE.ZhanGT4
namespace SeedData

/-- Protected moving marks and positive-time image noncollision suffice
for continuity of D10 away from the entrance. No lower seed-gap bound is used. -/
theorem continuousOn_d10Rate_of_clear {n : ℕ} (d : SeedData n)
    {A : Set ℂ} {T ρ : ℝ} (h : OwnData d.W A d.φ T d.a d.W') (hρ : 0 < ρ)
    (hV : ∀ m, ContinuousOn (d.V m) (Icc 0 T))
    (hclear : ∀ m t, t ∈ Icc (0 : ℝ) T →
      Disjoint (ball (d.V m t : ℂ) ρ) ((fun z => QuantumZipper.fwdMap d.W t z + d.W t) '' A))
    (h20 : ContinuousOn d.A20 (Icc 0 T))
    (hne20 : ∀ t ∈ Ioc (0 : ℝ) T, d.A 0 t ≠ d.A20 t)
    (hne : ∀ t ∈ Ioc (0 : ℝ) T, ∀ m, d.A 0 t ≠ d.B0 t m) :
    ContinuousOn d.d10Rate (Ioc 0 T) := by
  have hA0 := (h.continuousOn_frzA 0).mono Ioc_subset_Icc_self
  have hA1 := (h.continuousOn_frzA 1).mono Ioc_subset_Icc_self
  have hB (m : Fin n) : ContinuousOn (fun t => d.B0 t m) (Ioc 0 T) :=
    (Complex.continuous_re.comp_continuousOn
      (h.continuousOn_iterDeriv_moving hρ (hV m) (hclear m) 0)).mono Ioc_subset_Icc_self
  have hs : ContinuousOn (fun t => ∑ m, d.κ * d.r m / (d.A 0 t - d.B0 t m)) (Ioc 0 T) :=
    continuousOn_finsetSum _ fun m _ => continuousOn_const.div (hA0.sub (hB m))
      (fun t ht => sub_ne_zero.2 (hne t ht m))
  exact (hA1.pow 2).mul
    ((continuousOn_const.div (continuousOn_const.mul (hA0.sub (h20.mono Ioc_subset_Icc_self)))
      (fun t ht => mul_ne_zero (by norm_num) (sub_ne_zero.2 (hne20 t ht)))).neg.add hs)

end SeedData
end InteractingSLE.ZhanGT4
