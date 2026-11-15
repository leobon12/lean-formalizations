/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedCloseCoords

/-!
# Actual capacity force equations from the protected seed data

Packet PROVE-ZHAN-GT4-A22. The original seed entrance estimates and the
inverse clock give the force equations at every capacity time before the
image horizon. The protected other tip satisfies its own-time integrated
equation directly by the landed moving-clock chain rule.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

/-- The protected other tip has an ordinary entrance integral, by D3. -/
theorem SeedData.integrated_other_tip {n : ℕ} (s : SeedData n) {A : Set ℂ} {T : ℝ}
    (h : OwnData s.W A s.φ T s.a s.W') {v₀ : ℝ → ℂ}
    (hv₀ : QuantumZipper.IsForwardSol s.W' s.ζ₀ (s.a T) v₀)
    (hne : ∀ u ∈ Icc (0 : ℝ) T, s.A20 u ≠ s.A 0 u) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable (fun u => 2 * s.A 1 u ^ 2 / (s.A20 u - s.A 0 u)) volume 0 t ∧
      s.A20 t = s.A20 0 + ∫ u in (0 : ℝ)..t, 2 * s.A 1 u ^ 2 / (s.A20 u - s.A 0 u) := by
  have hd (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) := h.hasDerivWithinAt_frzImg hv₀ hu
  have hc : ContinuousOn s.A20 (Icc 0 T) := fun u hu => (hd u hu).continuousWithinAt
  have hr : ContinuousOn (fun u => 2 * s.A 1 u ^ 2 / (s.A20 u - s.A 0 u)) (Icc 0 T) :=
    (continuousOn_const.mul ((h.continuousOn_frzA 1).pow 2)).div
      (hc.sub (h.continuousOn_frzA 0)) (fun u hu => sub_ne_zero.2 (hne u hu))
  have hi : IntervalIntegrable (fun u => 2 * s.A 1 u ^ 2 / (s.A20 u - s.A 0 u))
      volume 0 t := (hr.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  refine ⟨hi, ?_⟩
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hc.mono (Icc_subset_Icc_right ht.2)) (fun u hu =>
      (hd u ⟨hu.1.le, hu.2.le.trans ht.2⟩).hasDerivAt
        (Icc_mem_nhds hu.1 (hu.2.trans_le ht.2))) hi
  change (∫ u in (0 : ℝ)..t, 2 * s.A 1 u ^ 2 / (s.A20 u - s.A 0 u)) =
    s.A20 t - s.A20 0 at he
  linarith only [he]

/-- The actual seed coordinates satisfy their force equations and have
integrable reciprocal gaps at every capacity time up to the image horizon.
The own seed entrance and protected interval estimates supply both facts. -/
theorem seedCapacitySeed_integrated {Ω : Type*} {n : ℕ} {d : Ω → SeedData n}
    {S : Ω → ℝ≥0} {A : Ω → Set ℂ} {c r L₀ : ℝ} {I : Ω → ℝ → Set ℝ}
    (hown : ∀ ω, OwnData (d ω).W (A ω) (d ω).φ (S ω) (d ω).a (d ω).W')
    (hCc : ∀ ω, Continuous (seedQuadClock (seedCapacityCoeff d S) ω))
    (hCs : ∀ ω, StrictMono (seedQuadClock (seedCapacityCoeff d S) ω))
    (hc : 0 < c) (hlb : ∀ ω t, c * t ≤ seedQuadClock (seedCapacityCoeff d S) ω t)
    (hr : 0 < r)
    (hI : ∀ ω t, t ∈ Icc (0 : ℝ) (S ω) → Convex ℝ (I ω t))
    (hWI : ∀ ω t, t ∈ Icc (0 : ℝ) (S ω) → (d ω).W t ∈ I ω t)
    (hVI : ∀ ω t, t ∈ Icc (0 : ℝ) (S ω) → ∀ m, (d ω).V m t ∈ I ω t)
    (hclear : ∀ ω t, t ∈ Icc (0 : ℝ) (S ω) → ∀ x ∈ I ω t,
      Disjoint (Metric.ball (x : ℂ) r)
        ((fun z => QuantumZipper.fwdMap (d ω).W t z + (d ω).W t) '' A ω))
    (hb : ∀ ω t, t ∈ Icc (0 : ℝ) (S ω) → ∀ x ∈ I ω t,
      deriv ((d ω).F 0 t) x ∈ Icc (Real.exp (-L₀)) (Real.exp L₀))
    (hseed : ∀ ω m, IsSeedCoordinate (d ω).W ((d ω).V m) (S ω))
    (ω : Ω) (m : Fin n) {u : ℝ≥0} (hu : u ≤ seedCapacityHorizon d S ω) :
    IntervalIntegrable (fun t : ℝ => (seedCapacityDriver d S t.toNNReal ω -
      seedCapacityForce d S m.succ t.toNNReal ω)⁻¹) volume 0 u ∧
      seedCapacityForce d S m.succ u ω = seedCapacityForce d S m.succ 0 ω +
        ∫ t in (0 : ℝ)..u, 2 / (seedCapacityForce d S m.succ t.toNNReal ω -
          seedCapacityDriver d S t.toNNReal ω) := by
  have hW (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (S ω)) :
      seedCapacityDriver d S ((d ω).a t).toNNReal ω = (d ω).A 0 t - (d ω).A 0 0 := by
    have hh := seedCapacityDriver_at_capacity hown hCc hCs hc hlb ω
      (show t.toNNReal ≤ S ω by simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal ht.2)
    simpa only [Real.coe_toNNReal _ ht.1] using hh
  have hV (j : Fin n) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (S ω)) :
      seedCapacityForce d S j.succ ((d ω).a t).toNNReal ω = (d ω).B0 t j - (d ω).A 0 0 := by
    have hh := seedCapacityForce_at_capacity hown hCc hCs hc hlb ω j.succ
      (show t.toNNReal ≤ S ω by simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal ht.2)
    simpa only [Real.coe_toNNReal _ ht.1, SeedData.imageForce, Fin.cases_succ] using hh
  obtain ⟨ht, hat⟩ := seedCapacityTime_spec hown hCc hCs hc hlb ω hu
  have hh := (d ω).capacity_image_seed (hown ω) hr (hI ω) (hWI ω) (hVI ω) (hclear ω) (hb ω)
    (hseed ω) (w := fun t => seedCapacityDriver d S t.toNNReal ω)
    (v := fun j t => seedCapacityForce d S j.succ t.toNNReal ω) hW hV m
    ⟨(seedCapacityTime d S u ω).coe_nonneg, ht⟩
  simpa only [hat, Real.toNNReal_coe, Real.toNNReal_zero] using hh

end InteractingSLE.ZhanGT4
