/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootD25Entry

/-!
# The actual normalized clock and the capacity of physical entry

Packet PROVE-T14-GW2ROOT2. The original protected traces supply the
normalized clock's continuity and strict increase. Its value at the
constructed physical entry is the actual sample's first crossing capacity.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootE26

open Exist Staged StagedLaw Restart Supp8.GB6 RootD25

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
  {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
  (hW : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hW0 : W 0 ω = 0)
  {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω) (hsH : α s ∈ H)
  {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
  (hγ : IsGeneratingTrace e.1 e.2 γ) {v : ℝ≥0}
  (hv : (v : ℝ≥0∞) < min
    (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
      ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) e.2)
  {a : ℝ≥0} (ha : 0 < a)

include hα hW hW0 hs hsH he hγ hv ha

/-- Normalization preserves the actual protected clock, including its endpoint. -/
theorem physicalClock_regular :
    let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
    physicalClock a s 0 p = 0 ∧
      StrictMonoOn (fun t => physicalClock a s t p) (Icc 0 v) ∧
      ContinuousOn (fun t => physicalClock a s t p) (Icc 0 v) := by
  obtain ⟨h0, hm, hc⟩ := RootZ21.forwardCapacity_regular_before_contact
    W ζ ω hα hW hW0 hs hsH he hγ hv
  refine ⟨?_, ?_, continuousOn_const.mul
    (continuous_real_toNNReal.comp_continuousOn hc)⟩
  · simp only [physicalClock, h0, Real.toNNReal_zero, mul_zero]
  · intro t ht u hu htu
    apply mul_lt_mul_of_pos_left _ (pow_pos ha 2)
    apply NNReal.coe_lt_coe.mp
    rw [Real.coe_toNNReal _ (RootZ21.forwardCapacity_nonneg _ _ _),
      Real.coe_toNNReal _ (RootZ21.forwardCapacity_nonneg _ _ _)]
    exact hm ht hu htu

/-- The inverse used by the physical entry reaches exactly the sample's
first crossing capacity; no relative-clock identity is assumed. -/
theorem physicalClock_entryPhysical
    (hreach : relativeSample a s v
      (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) ∈ reachSet) :
    let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
    physicalClock a s (entryPhysical a s v p) p =
      (entryCapacity (relativeSample a s v p)).toNNReal := by
  let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
  let τ := (entryCapacity (relativeSample a s v p)).toNNReal
  have hτcoe : (τ : ℝ≥0∞) = entryCapacity (relativeSample a s v p) :=
    ENNReal.coe_toNNReal (ne_top_of_lt (hreach.trans ENNReal.coe_lt_top))
  have hτ : τ < physicalClock a s v p := by
    apply ENNReal.coe_lt_coe.mp
    rw [hτcoe]
    exact hreach
  have hu : τ / a ^ 2 < (RootZ21.forwardCapacity s v p).toNNReal := by
    apply (div_lt_iff₀ (pow_pos ha 2)).mpr
    simpa only [physicalClock, mul_comm] using hτ
  have huR : ((τ / a ^ 2 : ℝ≥0) : ℝ) ≤ RootZ21.forwardCapacity s v p := by
    have h := NNReal.coe_lt_coe.mpr hu
    rw [Real.coe_toNNReal _ (RootZ21.forwardCapacity_nonneg _ _ _)] at h
    exact h.le
  have hc := (RootZ21.forwardClockInverse_spec_before_contact
    W ζ ω hα hW hW0 hs hsH he hγ hv (τ / a ^ 2) huR).2
  change physicalClock a s (entryPhysical a s v p) p = τ
  rw [entryPhysical, ite_eq_left hreach]
  change a ^ 2 * (RootZ21.forwardCapacity s
    (RootZ21.forwardClockInverse s v (τ / a ^ 2) p) p).toNNReal = τ
  rw [hc, Real.toNNReal_coe, mul_div_cancel₀ _ (pow_ne_zero 2 ha.ne')]

end InteractingSLE.Theorem14.GW2TipSystem.RootE26
