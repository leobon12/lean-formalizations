/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInActPoisson
import InteractingSLE.Spec.Sec6.Prop61Mean

/-!
# The actual local-set mean's full phase word on bounded components

PROVE-POCKET-SIDEIN. Aux. 27 supplies the subpower bound from the local-set
law. Aux. 29 then upgrades the incident corrected germs to the whole phase
word, excluding every fibre over the finite physical exceptional set. The
remaining `hIncident` is the precise boundary input to be produced by R.5.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric Bornology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets SupercriticalConformalCovariance PhaseSel

/-- Aux. 27's estimate measured against the local set gives the subpower
estimate at the boundary of each bounded active component. The deterministic
mean may be any harmonic function bounded on bounded subsets of H. -/
theorem ae_subpower_mean_on_bounded_components {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h g : Ω → DistOn upperHalfPlaneOpens}
    {K : Ω → Set ℂ} (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hKm : Measurable[mΩ, hittingSigma] K) (hKloc : IsLocalSet K h P)
    (hg : IsLocalSetMean K h P g) {F : ℂ → ℝ}
    (hFb : ∀ B : Set ℂ, IsBounded B → ∃ M : ℝ, ∀ z ∈ B ∩ H, |F z| ≤ M) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ K ω,
      IsBounded (connectedComponentIn (H \ K ω) z₀) → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ K ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ K ω →
        g ω φ = ∫ z, v z * φ z) →
      ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ,
        ∀ z ∈ connectedComponentIn (H \ K ω) z₀,
          |v z + F z| ≤ Cε *
            (1 + infDist z (frontier (connectedComponentIn (H \ K ω) z₀)) ^ (-ε)) := by
  filter_upwards [Sec6.ae_aux27_ball hh hKm hKloc hg, hKloc.2.1]
    with ω hbound ⟨_, hKo⟩ z₀ hz₀ hCb v hv hrep ε hε
  let C := connectedComponentIn (H \ K ω) z₀
  have hCV : C ⊆ H \ K ω := connectedComponentIn_subset _ _
  obtain ⟨r, hr⟩ := hCb.subset_ball (0 : ℂ)
  obtain ⟨n, hn⟩ := exists_nat_gt r
  have hCn : C ⊆ ball (0 : ℂ) n := hr.trans (ball_subset_ball hn.le)
  obtain ⟨MF, hMF⟩ := hFb (ball (0 : ℂ) n) Metric.isBounded_ball
  obtain ⟨B, hB⟩ := hbound n ε hε
  refine ⟨max B 0 + max MF 0, fun z hz => ?_⟩
  obtain ⟨hd, hdd⟩ := Sec6.infDist_frontier_le_infDist_union_real hKo hz
  have hpow := Real.rpow_le_rpow_of_nonpos hd hdd (neg_nonpos.2 hε.le)
  have hv' : |v z| ≤ max B 0 * (1 + infDist z (frontier C) ^ (-ε)) := by
    calc |v z| ≤ B * (1 + infDist z (K ω ∪ {w : ℂ | w.im = 0}) ^ (-ε)) :=
          hB v hv hrep z ⟨hCn hz, hCV hz⟩
      _ ≤ max B 0 * (1 + infDist z (K ω ∪ {w : ℂ | w.im = 0}) ^ (-ε)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _)
            (add_nonneg zero_le_one (Real.rpow_nonneg infDist_nonneg _))
      _ ≤ max B 0 * (1 + infDist z (frontier C) ^ (-ε)) :=
          mul_le_mul_of_nonneg_left (by linarith only [hpow]) (le_max_right _ _)
  have hF' : |F z| ≤ max MF 0 * (1 + infDist z (frontier C) ^ (-ε)) := by
    calc |F z| ≤ MF := hMF z ⟨hCn hz, (hCV hz).1⟩
      _ ≤ max MF 0 := le_max_left _ _
      _ ≤ max MF 0 * (1 + infDist z (frontier C) ^ (-ε)) := by
          exact le_mul_of_one_le_right (le_max_right _ _)
            (le_add_of_nonneg_right (Real.rpow_nonneg infDist_nonneg _))
  calc |v z + F z| ≤ |v z| + |F z| := abs_add_le _ _
    _ ≤ (max B 0 + max MF 0) * (1 + infDist z (frontier C) ^ (-ε)) := by
      rw [add_mul]
      exact add_le_add hv' hF'

/-- The whole phase word for an actual local-set mean. Only the incident
germs are a boundary input; the subpower and uniqueness steps are discharged. -/
theorem ae_phaseWord_on_bounded_components {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h g : Ω → DistOn upperHalfPlaneOpens}
    {K : Ω → Set ℂ} (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hKm : Measurable[mΩ, hittingSigma] K) (hKloc : IsLocalSet K h P)
    (hg : IsLocalSetMean K h P g) {F : ℂ → ℝ}
    (hF : InnerProductSpace.HarmonicOnNhd F H)
    (hFb : ∀ B : Set ℂ, IsBounded B → ∃ M : ℝ, ∀ z ∈ B ∩ H, |F z| ≤ M)
    {nL nR : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ K ω,
      IsBounded (connectedComponentIn (H \ K ω) z₀) → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ K ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ K ω →
        g ω φ = ∫ z, v z * φ z) →
      ∀ (vL : Fin (nL + 1) → ℝ) (vR : Fin (nR + 1) → ℝ) (d : ℝ),
      vL 0 ≤ 0 → 0 ≤ vR 0 → ∀ (f φ : ℂ → ℂ) (A : ℂ → ℝ) (E : Set ℂ),
      IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ K ω) z₀) →
      ContinuousOn f (closedBall 0 1) → E.Finite →
      E ⊆ frontier (connectedComponentIn (H \ K ω) z₀) →
      IsConformalBijection φ (connectedComponentIn (H \ K ω) z₀) H →
      ContinuousOn A (connectedComponentIn (H \ K ω) z₀) →
      (∀ z ∈ connectedComponentIn (H \ K ω) z₀,
        deriv φ z = ‖deriv φ z‖ * Complex.exp (A z * Complex.I)) →
      (∀ q ∈ sphere (0 : ℂ) 1, f q ∉ E → ∃ x : ℝ, x ∉ forceJumpSet vL vR ∧
        Tendsto (fun ζ => φ (f ζ)) (𝓝[ball 0 1] q) (𝓝[H] (x : ℂ)) ∧
        Tendsto (fun ζ => v (f ζ) + F (f ζ) + chiC κ * A (f ζ))
          (𝓝[ball 0 1] q) (𝓝 (phaseData κ ρL ρR vL vR d x))) →
      ∀ z ∈ connectedComponentIn (H \ K ω) z₀,
        v z + F z = phaseWordExt κ ρL ρR vL vR d (φ z) - chiC κ * A z := by
  filter_upwards [ae_subpower_mean_on_bounded_components hh hKm hKloc hg hFb,
    hKloc.2.1] with ω hbound ⟨_, hKo⟩ z₀ hz₀ hb v hv hrep
      vL vR d hL hR f φ A E hf hfc hE hEO hφ hAc hA hIncident
  have hCV := connectedComponentIn_subset (H \ K ω) z₀
  exact mean_eq_phaseWordExt_of_incident_germs hκ ρL ρR hL hR d
    hKo.connectedComponentIn hf hfc hE hEO
    (fun z hz => (hv z (hCV hz)).add (hF z (hCV hz).1))
    (hbound z₀ hz₀ hb v hv hrep) hφ hAc hA hIncident

end InteractingSLE.Sec7.PocketStopSide
