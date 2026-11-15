/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRAdvanceCont
import InteractingSLE.Spec.Sec7.PhaseSelAdaptCont

/-!
# GW4: finite stopping caps and continuity in component coordinates

The caps are the actual finite truncations `V ∧ n`. They cover every time below
`V`, including when `V = ∞`, and are stopping times whenever `V` is one. The
continuity adapter uses the landed canonical encoding of the relative driver.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open Restart Supp8.Q3Stop Sec7.PhaseSel Sec7.PocketTraversal MartChar

/-- The finite cap `V ∧ n`, represented as an NNReal time. -/
def gw4PhaseCap {Ω : Type*} (V : Ω → ℝ≥0∞) (n : ℕ) (ω : Ω) : ℝ≥0 :=
  (min (V ω) (n : ℝ≥0∞)).toNNReal

/-- The finite truncation has its intended value even when `V = ∞`. -/
theorem coe_gw4PhaseCap {Ω : Type*} (V : Ω → ℝ≥0∞) (n : ℕ) (ω : Ω) :
    (gw4PhaseCap V n ω : ℝ≥0∞) = min (V ω) (n : ℝ≥0∞) :=
  ENNReal.coe_toNNReal ((lt_of_le_of_lt (min_le_right _ _) (ENNReal.natCast_lt_top n)).ne)

/-- Finite truncations of a stopping lifetime are stopping times. -/
theorem isStoppingTime_gw4PhaseCap {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ} {V : Ω → ℝ≥0∞} (hV : IsStoppingTime 𝓕 V) (n : ℕ) :
    IsStoppingTime 𝓕 fun ω => (gw4PhaseCap V n ω : WithTop ℝ≥0) := by
  have he : (fun ω => (gw4PhaseCap V n ω : WithTop ℝ≥0)) =
      fun ω => min (V ω) (n : WithTop ℝ≥0) := funext (coe_gw4PhaseCap V n)
  rw [he]
  exact hV.min (isStoppingTime_const 𝓕 (n : ℝ≥0))

/-- Every finite cap is at most the lifetime. -/
theorem gw4PhaseCap_le {Ω : Type*} (V : Ω → ℝ≥0∞) (n : ℕ) (ω : Ω) :
    (gw4PhaseCap V n ω : ℝ≥0∞) ≤ V ω := by
  rw [coe_gw4PhaseCap]
  exact min_le_left _ _

/-- The finite caps cover all relative times strictly before the lifetime. -/
theorem exists_le_gw4PhaseCap {Ω : Type*} {V : Ω → ℝ≥0∞} {ω : Ω} {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < V ω) : ∃ n, q ≤ gw4PhaseCap V n ω := by
  obtain ⟨n, hn⟩ := exists_nat_ge q
  refine ⟨n, ENNReal.coe_le_coe.1 ?_⟩
  rw [coe_gw4PhaseCap]
  exact le_min hq.le (by exact_mod_cast hn)

/-- Continuity of every extension choice in the exact component-coordinate
form used by Aux. 122. Constancy is required only at positive times through
the indicated finite cap; the phase value at zero is arbitrary. -/
theorem continuousOn_componentMean_of_positive_phase_const {Ω : Type*}
    {k : ℝ} {c₀ : BoundaryWord} {X : Ω → DistOn upperHalfPlaneOpens}
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hR0 : ∀ ω, R 0 ω = 0) (hRc : ∀ ω, Continuous (R · ω))
    {d : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ≥0 → ℂ → ℝ}
    (hU : ∀ ω q, IsBoundedHarmonicExtension
      (phaseData k (typedRhoL (wordType k c₀)) (typedRhoR (wordType k c₀))
        (fun i => componentVL k c₀ X R V i q ω - R q ω)
        (fun j => componentVR k c₀ X R V j q ω - R q ω) (d q ω))
      (forceJumpSet (fun i => componentVL k c₀ X R V i q ω - R q ω)
        (fun j => componentVR k c₀ X R V j q ω - R q ω)) (U ω q))
    {ω : Ω} {c : ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hd : ∀ q, 0 < q → q ≤ T.toNNReal → d q ω = c)
    {z : ℂ} (hz : z ∈ H \ fwdHull (wpath R ω) T) :
    ContinuousOn (fun q : ℝ => couplingMean k (wpath R ω) q (U ω q.toNNReal) z)
      (Icc 0 T) := by
  have hVL : componentVL k c₀ X R V =
      geomLW R (fun _ => typedXL k (wordType k c₀) c₀) := by
    funext i q ω
    exact componentVL_eq_geom k c₀ X R V (hRc ω) (hR0 ω) i q
  have hVR : componentVR k c₀ X R V =
      geomRW R (fun _ => typedXR k (wordType k c₀) c₀) := by
    funext j q ω
    exact componentVR_eq_geom k c₀ X R V (hRc ω) (hR0 ω) j q
  have hLc : ∀ i, Continuous fun q => componentVL k c₀ X R V i q ω := by
    rw [hVL]
    exact fun i => (isForcePath_geomLW hRc _ ω i).1
  have hRc' : ∀ j, Continuous fun q => componentVR k c₀ X R V j q ω := by
    rw [hVR]
    exact fun j => (isForcePath_geomRW hRc _ ω j).1
  have hLo : ∀ q i, componentVL k c₀ X R V i q ω ≤ R q ω := by
    rw [hVL]
    exact fun q i => geomLW_le hRc _ ω q i
  have hRo : ∀ q j, R q ω ≤ componentVR k c₀ X R V j q ω := by
    rw [hVR]
    exact fun q j => le_geomRW hRc _ ω q j
  have hseed := (component_seeds_zero k c₀ X R V ω).1.trans
    (component_seeds_zero k c₀ X R V ω).2.symm
  exact continuousOn_couplingMean_of_positive_phase_const (hRc ω) hLc hRc' hLo hRo hseed
    (hU ω) hT hd hz

end InteractingSLE.Theorem14.GW4Fix
