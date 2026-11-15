/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootD25Regular
import InteractingSLE.Spec.Supplement.GW2RootD25Passage

/-!
# Constructing the actual physical entry time

Packet PROVE-T14-GW2ROOT2. Pull the measurable sample's first crossing
back by the actual inverse clock. On failure use the physical buffer
cutoff. On a protected original trace, success puts this time strictly
before the cutoff and the actual physical-time driver is exactly two.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootD25

open Exist Staged StagedLaw Restart Supp8.GB6 RootB23

/-- The first crossing in original physical time, capped at failure. -/
def entryPhysical (a s v : ℝ≥0) (p : RecData × RecData) : ℝ≥0 :=
  open scoped Classical in
  if relativeSample a s v p ∈ reachSet then
    RootZ21.forwardClockInverse s v
      ((entryCapacity (relativeSample a s v p)).toNNReal / a ^ 2) p else v

theorem measurable_entryPhysical (a s v : ℝ≥0) : Measurable (entryPhysical a s v) := by
  classical
  have ht := ((measurable_entryCapacity.comp
    (measurable_relativeSample a s v)).ennreal_toNNReal).div_const (a ^ 2)
  exact Measurable.ite ((measurable_relativeSample a s v) measurableSet_reachSet)
    (measurable_forwardClockInverse_random measurable_id ht s v) measurable_const

theorem entryPhysical_eq_cutoff {a s v : ℝ≥0} {p : RecData × RecData}
    (hfail : relativeSample a s v p ∉ reachSet) : entryPhysical a s v p = v :=
  ite_eq_right hfail

/-- On the original protected trace a successful measurable sample has
its actual entry before the physical cutoff, at driver value exactly two. -/
theorem entryPhysical_spec_before_contact {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
    (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
    {s : ℝ≥0} (hsH : α s ∈ H)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace e.1 e.2 γ) {v : ℝ≥0}
    (hv : (v : ℝ≥0∞) < min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) e.2)
    {a : ℝ≥0} (ha : 0 < a)
    (hreach : relativeSample a s v
      (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) ∈ reachSet) :
    let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
    entryPhysical a s v p < v ∧
      (physicalObservationRead a s v (entryPhysical a s v p) p).1 = 2 := by
  let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
  let z := relativeSample a s v p
  let τ := (entryCapacity z).toNNReal
  let u := τ / a ^ 2
  have hs : (s : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  have hτcoe : (τ : ℝ≥0∞) = entryCapacity z :=
    ENNReal.coe_toNNReal (ne_top_of_lt (hreach.trans (ENNReal.coe_lt_top)))
  have hτ : τ < physicalClock a s v p := by
    apply ENNReal.coe_lt_coe.mp
    rw [hτcoe]
    exact hreach
  have hu : u < (RootZ21.forwardCapacity s v p).toNNReal := by
    apply (div_lt_iff₀ (pow_pos ha 2)).mpr
    simpa only [physicalClock, mul_comm] using hτ
  have huR : (u : ℝ) < RootZ21.forwardCapacity s v p := by
    have hh := NNReal.coe_lt_coe.mpr hu
    rwa [Real.coe_toNNReal _ (RootZ21.forwardCapacity_nonneg _ _ _)] at hh
  have hspec := RootZ21.forwardClockInverse_spec_before_contact
    W ζ ω hα hW.continuousOn hW0 hs hsH he hγ hv u huR.le
  have hent : entryPhysical a s v p = RootZ21.forwardClockInverse s v u p :=
    ite_eq_left hreach
  have htv : entryPhysical a s v p < v := by
    rw [hent]
    apply lt_of_le_of_ne hspec.1
    intro heq
    have hh := hspec.2
    rw [heq] at hh
    exact huR.ne hh.symm
  obtain ⟨_, hc, _⟩ := relative_readers_generatingTrace_before_contact
    W ζ ω hα hW hW0 hζ hsH he hγ hv
  have hcY : ContinuousOn (fun t => scaledRelativeDriverRead a s v t p)
      {t | (t : ℝ≥0∞) < z.1} := by
    simpa only [z, relativeSample, physicalClock, scaledRelativeDriverRead, ENNReal.coe_mul]
      using Sec5.Prop59NodeTree.continuousOn_scale ha hc
  have htwo := driver_eq_two_at_entry hcY (scaledRelativeDriverRead_zero _ _ _ _)
    (fun q hq => relativeSample_read a s v p hq) hτcoe.symm
  refine ⟨htv, ?_⟩
  rw [physicalObservationRead_eq ha, hent, hspec.2, Real.toNNReal_coe]
  exact htwo

end InteractingSLE.Theorem14.GW2TipSystem.RootD25
