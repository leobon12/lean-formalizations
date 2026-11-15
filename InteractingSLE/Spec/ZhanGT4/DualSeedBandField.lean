/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedBandScale

/-!
# Analytic data for a band of a random field

Packet PROVE-ZHAN-GT4-A22. These are local derivative and continuity
conditions. The finite-pasting estimate is proved from them.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {S : Ω → ℝ≥0}
  {Φ Φ₁ Φ₂ Φ₃ Ψ : ℝ → Ω → ℝ → ℝ} {ρ K : ℝ}

/-- Regularity in Brownian spatial coordinates on a moving tube. No
stochastic identity or Taylor-error estimate is part of this predicate. -/
structure SeedRegularBand (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0)
    (Φ Φ₁ Φ₂ Φ₃ Ψ : ℝ → Ω → ℝ → ℝ) (ρ K : ℝ) : Prop where
  radius_pos : 0 < ρ
  bound_nonneg : 0 ≤ K
  local_field : ∀ ω (a b y : ℝ), 0 ≤ a → a ≤ b → b ≤ S ω →
    (∀ u ∈ Icc a b, |B u.toNNReal ω - y| < ρ) →
    IsLogField (fun u x => Φ u ω x) (fun u x => Φ₁ u ω x) (fun u x => Φ₂ u ω x)
      (fun u x => Φ₃ u ω x) (fun u x => Ψ u ω x) a b y ρ K
  cont : ∀ ω, ContinuousOn (fun p : ℝ × ℝ => Φ p.1 ω p.2)
    (seedPathTube (fun u => B u.toNNReal ω) 0 (S ω) (3 * ρ))
  contX : ∀ ω, ContinuousOn (fun p : ℝ × ℝ => Φ₁ p.1 ω p.2)
    (seedPathTube (fun u => B u.toNNReal ω) 0 (S ω) (3 * ρ))
  contT : ∀ ω, ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 ω p.2)
    (seedPathTube (fun u => B u.toNNReal ω) 0 (S ω) (3 * ρ))
  contXX : ∀ ω, ContinuousOn (fun p : ℝ × ℝ => Φ₂ p.1 ω p.2)
    (seedPathTube (fun u => B u.toNNReal ω) 0 (S ω) (3 * ρ))

namespace SeedRegularBand

variable (h : SeedRegularBand B S Φ Φ₁ Φ₂ Φ₃ Ψ ρ K)
include h

/-- The stopped spatial coefficients inherit the band bound. -/
theorem coef_bound (ω : Ω) (u : ℝ≥0) :
    |Ito.stopCoef Φ₁ B S u ω| ≤ K ∧ |Ito.stopCoef Φ₂ B S u ω| ≤ K := by
  by_cases hu : u < S ω
  · have hl := h.local_field ω u u (B u ω) u.coe_nonneg le_rfl hu.le
      (fun v hv => by
        rw [show v = (u : ℝ) from le_antisymm hv.2 hv.1, Real.toNNReal_coe, sub_self, abs_zero]
        exact h.radius_pos)
    have hb := hl.bound u ⟨le_rfl, le_rfl⟩ (B u ω) (by
      simp only [sub_self, abs_zero]; linarith only [h.radius_pos])
    simpa only [Ito.stopCoef, ite_eq_left hu] using ⟨hb.2.1, hb.2.2.1⟩
  · simp only [Ito.stopCoef, ite_eq_right hu, abs_zero]
    exact ⟨h.bound_nonneg, h.bound_nonneg⟩

/-- The compensated stopped field is continuous. In particular continuity
at the stopping boundary is a consequence of the field data. -/
theorem continuous_stopped (hB : ∀ ω, Continuous (B · ω)) (ω : Ω) :
    Continuous (Ito.fieldStopped Φ Φ₂ Ψ B S 0 · ω) := by
  let β : ℝ → ℝ := fun u => B u.toNNReal ω
  have hβ : Continuous β := (hB ω).comp continuous_real_toNNReal
  have hm : MapsTo (fun u => (u, β u)) (Icc 0 (S ω : ℝ))
      (seedPathTube β 0 (S ω) (3 * ρ)) := fun u hu =>
    ⟨hu, by simp only [sub_self, abs_zero]; linarith only [h.radius_pos]⟩
  have hmap : ContinuousOn (fun u => (u, β u)) (Icc 0 (S ω : ℝ)) :=
    continuousOn_id.prodMk hβ.continuousOn
  have h0 := (h.cont ω).comp hmap hm
  have hg : ContinuousOn (fun u => Ito.fieldGen Φ₂ Ψ B u ω) (Icc 0 (S ω : ℝ)) :=
    ((h.contT ω).comp hmap hm).add
      (continuousOn_const.mul ((h.contXX ω).comp hmap hm))
  have hi : IntegrableOn (fun u => Ito.fieldGen Φ₂ Ψ B u ω) (uIcc 0 (S ω : ℝ)) := by
    rw [uIcc_of_le (S ω).coe_nonneg]
    exact hg.integrableOn_Icc
  have hJ := intervalIntegral.continuousOn_primitive_interval hi
  rw [uIcc_of_le (S ω).coe_nonneg] at hJ
  have hc : Continuous (fun u : ℝ≥0 => ((min u (S ω) : ℝ≥0) : ℝ)) :=
    NNReal.continuous_coe.comp (continuous_id.min continuous_const)
  have hcm : ∀ u : ℝ≥0, ((min u (S ω) : ℝ≥0) : ℝ) ∈ Icc 0 (S ω : ℝ) :=
    fun u => ⟨(min u (S ω)).coe_nonneg, min_le_right _ _⟩
  convert (h0.comp_continuous hc hcm).sub (hJ.comp_continuous hc hcm) using 1
  funext u
  simp only [Function.comp_apply, Pi.sub_apply, Ito.fieldStopped, β, Real.toNNReal_coe]

/-- Actual band pasting, including the stopping boundary. -/
theorem taylor_bound (hB : ∀ ω, Continuous (B · ω)) (t : ℝ≥0) (ω : Ω) :
    ∃ (C : ℝ) (R : ℕ → ℝ), Tendsto R atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
      |seedDyadicDefect (Ito.fieldStopped Φ Φ₂ Ψ B S 0)
        (Ito.stopCoef Φ₁ B S) (Ito.stopCoef Φ₂ B S) B n t ω| ≤
          C * seedCubicError B n t ω + R n :=
  seed_stopped_field_taylor_bound t ω h.radius_pos h.bound_nonneg (hB ω)
    (h.continuous_stopped hB ω) (h.local_field ω) (h.contT ω) (h.contXX ω)
    (fun u _ => (h.coef_bound ω u).1) (fun u _ => (h.coef_bound ω u).2)

end SeedRegularBand

end InteractingSLE.ZhanGT4
