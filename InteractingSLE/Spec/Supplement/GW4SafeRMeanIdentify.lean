/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRMeanInputs

/-!
# GW4: finite-word mean identification with zero phase

This is a conditional analytic reduction, using exactly the named open inputs
in `GW4SafeRMeanInputs`. The phase is selected by Aux. 122 rather than assumed
zero. The conclusion is the shared mean interface consumed with CLOC's locality.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.GW4Fix

open Restart WholeField LocalSets Supp8.Q3Stop Sec7.PocketTraversal

/-- Aux. 122 eliminates the actual component phase on every positive time
strictly before its lifetime, with the exact typed geometric coordinates. -/
theorem ComponentPhaseCaps.ae_phase_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {k : ℝ} {c₀ : BoundaryWord} {ν : Measure Ω}
    {X : Ω → DistOn upperHalfPlaneOpens} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (h : ComponentPhaseCaps k c₀ ν X R V) (hk : 4 < k)
    (hL : -2 < typedRhoL (wordType k c₀) (componentSeedL k c₀))
    (hR : -2 < typedRhoR (wordType k c₀) (componentSeedR k c₀))
    (hR0 : ∀ ω, R 0 ω = 0) (hRc : ∀ ω, Continuous (R · ω)) :
    ∀ᵐ ω ∂ν, ∀ q : ℝ≥0, 0 < q → (q : ℝ≥0∞) < V ω → h.phase q ω = 0 := by
  have := h.probability
  have := h.rightContinuous
  have hVL : componentVL k c₀ X R V =
      geomLW R (fun _ => typedXL k (wordType k c₀) c₀) := by
    funext i q ω
    exact componentVL_eq_geom k c₀ X R V (hRc ω) (hR0 ω) i q
  have hVR : componentVR k c₀ X R V =
      geomRW R (fun _ => typedXR k (wordType k c₀) c₀) := by
    funext j q ω
    exact componentVR_eq_geom k c₀ X R V (hRc ω) (hR0 ω) j q
  have hm := h.martingales
  have hc := h.continuity
  rw [hVL, hVR] at hm hc
  refine ae_phase_eq_zero_geom_caps hk hL h.seedL_upper
    hR h.seedR_upper hR0 hRc h.adapted measurable_const measurable_const
    (fun _ => ?_) (fun _ => ?_) (fun _ i => ?_) (fun _ j => ?_)
    (fun _ => antitone_typedXL _ _ _) (fun _ => monotone_typedXR _ _ _)
    h.stopping h.cover h.quantized hm hc
  · rw [typedXL_self_eq]
    rfl
  · rw [typedXR_self_eq]
    rfl
  · rw [typedXL_self_eq]
    exact GW0.flowLineXL_lt _ _ 0 (Fin.succ_pos i)
  · rw [typedXR_self_eq]
    exact GW0.flowLineXR_lt _ _ 0 (Fin.succ_pos j)

/-- The exact shared finite-word mean follows from the phase-word boundary
representation and its protected martingales. The zero relative time is covered
by coincident seeds, so no value of the phase at time zero is postulated. -/
theorem componentLineMean_of_phaseInputs {Ω : Type*} [MeasurableSpace Ω]
    {k : ℝ} (hk : 4 < k) {c₀ : BoundaryWord} {F : Frame} {ν : Measure Ω}
    {X : Ω → DistOn upperHalfPlaneOpens} {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω}
    {V : Ω → ℝ≥0∞} {hWm : ∀ r, Measurable (Wd r)} {u₀ : ℂ → ℝ}
    {ℋ : ℝ≥0 → MeasurableSpace Ω} {B : ℝ≥0 → Ω → Set ℂ}
    (hloc : ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B)
    (hL : -2 < typedRhoL (wordType k c₀) (componentSeedL k c₀))
    (hR : -2 < typedRhoR (wordType k c₀) (componentSeedR k c₀))
    (hR0 : ∀ ω, R 0 ω = 0) (hRc : ∀ ω, Continuous (R · ω))
    (hcap : ComponentPhaseCaps k c₀ ν X R V)
    (hrep : ComponentPhaseRepresentation k c₀ F ν X Wd GT R V u₀ B hcap.phase) :
    ComponentLineMean k c₀ F ν X Wd GT R V u₀ B := by
  have hz := hcap.ae_phase_eq_zero hk hL hR hR0 hRc
  intro t g hg ψ
  filter_upwards [hz, hrep t g hg, hloc.2.2.2.2.2.2 t] with ω hzero hrepr hshape hlt hψ
  obtain ⟨w, G, hw, hpair, hG, hm⟩ := hrepr hlt
  have hqV : ((lineClock F Wd GT V t ω).toNNReal : ℝ≥0∞) < V ω := by
    rw [ENNReal.coe_toNNReal (ne_top_of_lt hlt)]
    exact hlt
  have hd : hcap.phase (lineClock F Wd GT V t ω).toNNReal ω = 0 ∨
      componentVL k c₀ X R V (componentSeedL k c₀)
        (lineClock F Wd GT V t ω).toNNReal ω =
      componentVR k c₀ X R V (componentSeedR k c₀)
        (lineClock F Wd GT V t ω).toNNReal ω := by
    by_cases hq : (lineClock F Wd GT V t ω).toNNReal = 0
    · right
      rw [hq, (component_seeds_zero k c₀ X R V ω).1,
        (component_seeds_zero k c₀ X R V ω).2]
    · exact Or.inl (hzero _ (pos_iff_ne_zero.2 hq) hqV)
  exact pairing_eq_couplingMean_of_phase
    ((hRc ω).comp continuous_real_toNNReal) (hshape hlt) hw hloc.1.1 hpair hm hG hd hψ

end InteractingSLE.Theorem14.GW4Fix
