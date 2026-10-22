import HigherDimLQGContinuity.Rotation.Limits
import HigherDimLFPP.Field.Exists

/-!
# Rotation invariance in law of strong exponential metrics

The canonical metric of `HigherDimLQGMetric.theorem12` is the local-uniform probability limit of
rotation-covariant LFPP approximations. Uniqueness in that theorem transfers covariance to every
strong assignment, and invariance of the normalized field gives equality of push-forward laws.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

private lemma rot_mem_sqBall (O : Rd d ≃ₗᵢ[ℝ] Rd d)
    (R : ℝ) (p : Rd d × Rd d) (hp : p ∈ rotSqBall d R) :
    (O p.1, O p.2) ∈ rotSqBall d R := by
  obtain ⟨h1, h2⟩ := hp
  rw [mem_closedBall_zero_iff] at h1 h2
  exact ⟨by simpa only [mem_closedBall_zero_iff, O.norm_map] using h1,
    by simpa only [mem_closedBall_zero_iff, O.norm_map] using h2⟩

/-- Every strong exponential metric at the distance exponent has an orthogonally invariant law
under the canonical normalized whole-space LGF. -/
theorem strongRotLaw_holds {d : ℕ} (hd : 3 ≤ d) : StrongRotLaw d := by
  intro ξ hξ hgap D hD O
  let μ := normLGFLaw d
  have hspec := normLGFLaw_spec d (by omega : 2 ≤ d)
  letI : IsProbabilityMeasure μ := hspec.1
  have hLGF : IsWholeSpaceLGF (id : DistRd d → DistRd d) μ := hspec.2.1.1
  obtain ⟨⟨D₀, hD₀, hconv⟩, huniq⟩ := theorem12 d ξ hd hξ hgap
  have hcanon : ∀ᵐ g ∂μ, ∀ p : Rd d × Rd d,
      (D₀ (rotDistRd O g)).1 p = (D₀ g).1 (O p.1, O p.2) := by
    obtain ⟨κ, hκ⟩ := HigherDimLFPP.exists_isLFPPKernel d
    have hX := hconv κ hκ μ id hLGF.isLGFPlusBddCont
    have hX' := hconv κ hκ μ (rotDistRd O)
      (isWholeSpaceLGF_rotDistRd hLGF O).isLGFPlusBddCont
    have hXX' : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ g ∂μ,
        ∀ p : Rd d × Rd d,
        ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (rotDistRd O g)) p =
        ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε g) (O p.1, O p.2) := by
      exact Eventually.of_forall fun ε => ae_of_all _ fun g p => by
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [lfppDist_rotDistRd]
    exact rot_ae_eq_comp_of_tendstoInProbLU
      (T := fun p : Rd d × Rd d => (O p.1, O p.2))
      (fun R p hp => rot_mem_sqBall O R p hp) hX hX' hXX'
  obtain ⟨C, hC, hrel⟩ := huniq D₀ D hD₀ hD
  have hrel_id : ∀ᵐ g ∂μ, ∀ p : Rd d × Rd d,
      (D g).1 p = C * (D₀ g).1 p := by
    filter_upwards [hrel μ id hLGF.isLGFPlusCont] with g hg p
    simpa only [id_eq, addFun_zero] using hg 0 p.1 p.2
  have hrel_rot : ∀ᵐ g ∂μ, ∀ p : Rd d × Rd d,
      (D (rotDistRd O g)).1 p = C * (D₀ (rotDistRd O g)).1 p := by
    filter_upwards [hrel μ (rotDistRd O)
      (isWholeSpaceLGF_rotDistRd hLGF O).isLGFPlusCont] with g hg p
    simpa only [addFun_zero] using hg 0 p.1 p.2
  have hae : ∀ᵐ g ∂μ, ∀ p : Rd d × Rd d,
      (D (rotDistRd O g)).1 p = (D g).1 (O p.1, O p.2) := by
    filter_upwards [hcanon, hrel_id, hrel_rot] with g hg0 hg1 hg2 p
    rw [hg2 p, hg0 p, ← hg1 (O p.1, O p.2)]
  let F : DistRd d → C(Rd d × Rd d, ℝ) := fun g => (D g).1
  have hF : Measurable F := measurable_subtype_coe.comp hD.measurable
  let O₂ : C(Rd d × Rd d, Rd d × Rd d) :=
    ⟨fun p => (O p.1, O p.2),
      (O.continuous.comp continuous_fst).prodMk (O.continuous.comp continuous_snd)⟩
  have hrot : Measurable (rotDistRd O) := measurable_rotDistRd O
  change μ.map (fun g => (D g).1.comp O₂) = μ.map F
  calc
    μ.map (fun g => (D g).1.comp O₂) =
        μ.map (fun g => (D (rotDistRd O g)).1) := by
      apply Measure.map_congr
      filter_upwards [hae] with g hg
      apply ContinuousMap.ext
      intro p
      exact (hg p).symm
    _ = (μ.map (rotDistRd O)).map F := by
      exact (Measure.map_map hF hrot).symm
    _ = μ.map F := by rw [map_rotDistRd_normLGFLaw (by omega) O]

end HigherDimLQGContinuity
