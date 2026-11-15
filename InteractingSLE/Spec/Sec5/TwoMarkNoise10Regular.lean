/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkNoise10Mart

/-!
# Regularity and bounds for the stopped local noise

The stopped inverse clock stays in a compact clock interval. Continuity of the
existing inverse there and compact source observable bounds give the required
all-sample continuity and uniform bounds.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Noise10

open Zhan.Retarget

variable {Ω : Type*} {κ a b : ℝ} {xL ρL : Fin 0 → ℝ} {ρR : Fin 2 → ℝ}
  {W B : ℝ≥0 → Ω → ℝ} {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 2 → ℝ≥0 → Ω → ℝ}
  {e : Ω → ℝ≥0∞} {S : ℕ → Ω → ℝ≥0} {G : Set Ω}

/-- The capped inverse-time coordinate process has continuous paths. -/
theorem continuous_cappedPoint (ha : 0 < a) (hab : a < b)
    (hgood : ∀ ω ∈ G, Mart9.IsGood κ a b xL ρL ρR W B VL VR e S ω)
    (hZc : ∀ n ω, Continuous
      (Adapt8.stoppedCoords xL ![a, b] a 0 G W B VL VR (rLoc 0 G S W VL VR B e n) · ω))
    (n : ℕ) (ω : Ω) : Continuous (cappedPoint xL a b G S W B VL VR e n · ω) := by
  by_cases hω : ω ∈ G
  · have hg := hgood ω hω
    let σ := rLoc 0 G S W VL VR B e n ω
    let Q := imageStops a G S W B VL VR e n ω
    have hs : SepUpTo (W · ω) (VR 0 · ω)
      (sepTime (W · ω) (VR 0 · ω) (e ω)) := (hg.data ha hab).sep
    have hR := (hs.isSep_of_lt (hg.loc_lt (G := G) n)).isRate ha
    have h0 := (clk_lt_newHorizon' hs ha (hg.loc_lt (G := G) n)).1
    have hQ : (Q : ℝ) = clk (rate a (W · ω) (VR 0 · ω)) σ := by
      simp only [Q, imageStops, Clock7.imageStop, hω, ↓reduceIte]
      exact Real.coe_toNNReal _ h0
    let t : ℝ≥0 → ℝ≥0 := fun u => (invClk (rate a (W · ω) (VR 0 · ω)) (min u Q : ℝ≥0)).toNNReal
    have ht : Continuous t := by
      refine continuous_real_toNNReal.comp (hR.continuousOn_invClk.comp_continuous
        (NNReal.continuous_coe.comp (continuous_id.min continuous_const)) fun u => ?_)
      refine ⟨(min u Q).coe_nonneg, ?_⟩
      rw [← hQ]
      exact_mod_cast min_le_right u Q
    have he : (cappedPoint xL a b G S W B VL VR e n · ω) =
        fun u => Adapt8.stoppedCoords xL ![a, b] a 0 G W B VL VR
          (rLoc 0 G S W VL VR B e n) (t u) ω := by
      funext u
      have hle : t u ≤ σ := by
        rw [show t u = _ from (min_cap_inverse_localizer ha hab hg hω n u).symm]
        exact min_le_right _ _
      simp only [cappedPoint, Adapt8.stoppedCoords, min_cap_inverse_localizer ha hab hg hω n u]
      rw [min_eq_left hle]
    rw [he]
    exact (hZc n ω).comp ht
  · simp only [cappedPoint, Adapt8.stoppedCoords, rCoord, hω, ↓reduceIte]
    exact continuous_const

/-- Every stopped masked-noise path is continuous. -/
theorem continuous_localNoise_stopped (hκ : 0 < κ) (ha : 0 < a) (hab : a < b)
    (hgood : ∀ ω ∈ G, Mart9.IsGood κ a b xL ρL ρR W B VL VR e S ω)
    (hZc : ∀ n ω, Continuous
      (Adapt8.stoppedCoords xL ![a, b] a 0 G W B VL VR (rLoc 0 G S W VL VR B e n) · ω))
    (n : ℕ) (ω : Ω) : Continuous fun u => localNoise κ a b xL ρL ρR G W B VL VR
      (min u (imageStops a G S W B VL VR e n ω)) ω := by
  simp only [localNoise_min_eq hκ ha hab hgood]
  have hc := (contDiffOn_obs κ xL ![a, b] ρL ρR 0 (n := 0)).continuousOn.comp_continuous
    (continuous_cappedPoint ha hab hgood hZc n ω) (fun u => ?_)
  · exact (hc.sub continuous_const).div_const _
  · exact rKc_subset_obsRegion κ xL ![a, b] ρL ρR 0 a (Mart9.initial_mem_region ha hab) n
      (Mart9.stoppedCoords_mem_orderedBox ha hab hgood n _ ω).1

/-- Each stopped masked-noise process has a uniform deterministic bound. -/
theorem exists_bound_localNoise_stopped (hκ : 0 < κ) (ha : 0 < a) (hab : a < b)
    (hgood : ∀ ω ∈ G, Mart9.IsGood κ a b xL ρL ρR W B VL VR e S ω) (n : ℕ) :
    ∃ C, ∀ u ω, |localNoise κ a b xL ρL ρR G W B VL VR
      (min u (imageStops a G S W B VL VR e n ω)) ω| ≤ C := by
  obtain ⟨C, hC⟩ := Mart9.exists_bound_stopped_observable ha hab hgood
    (contDiffOn_obs κ xL ![a, b] ρL ρR 0 (n := 0)).continuousOn n
  let c := obs κ xL ![a, b] ρL ρR 0 (rInit xL ![a, b] a)
  refine ⟨(C + |c|) / Real.sqrt κ, fun u ω => ?_⟩
  rw [localNoise_min_eq hκ ha hab hgood, abs_div, abs_of_nonneg (Real.sqrt_nonneg κ)]
  refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg κ)
  exact (abs_sub _ _).trans (add_le_add (hC _ ω) le_rfl)

end InteractingSLE.Sec5.TwoMark.Noise10
