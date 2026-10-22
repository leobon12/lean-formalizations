import HigherDimLQGMetric.LfppTight.PureProperTail

/-! The normalized LGF closure laws have proper continuous metrics. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_pure_closure_proper (hL1e : L1e_law)
    {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    (μ : ProbabilityMeasure C(Rd d × Rd d, ℝ))
    (hμ : μ ∈ closure {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
      ∃ ε ∈ Ioo (0 : ℝ) 1,
        (ν : Measure C(Rd d × Rd d, ℝ)) =
          P.map (fun ω => toCMapRd
            ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)))}) :
    ∀ᵐ (D : C(Rd d × Rd d, ℝ)) ∂(μ : Measure C(Rd d × Rd d, ℝ)),
      IsProperFn (d := d) D := by
  classical
  letI : PolishSpace C(Rd d × Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  let B : ℝ → Ω → C(Rd d × Rd d, ℝ) := fun ε ω =>
    toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))
  let S : Set (ProbabilityMeasure C(Rd d × Rd d, ℝ)) :=
    {ν | ∃ ε ∈ Ioo (0 : ℝ) 1,
      (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (B ε)}
  change μ ∈ closure S at hμ
  have hForall (n : ℕ) :
      ∀ᵐ D ∂(μ : Measure C(Rd d × Rd d, ℝ)),
        ∃ R : ℝ, (n : ℝ) < R ∧
          (n : ℝ) ≤ DGZ.nd_setInf (closedBall (0 : Rd d) n) (sphere 0 R) D := by
    let F : ℝ → Set C(Rd d × Rd d, ℝ) := fun R =>
      {D | (n : ℝ) < R ∧
        (n : ℝ) ≤ DGZ.nd_setInf (closedBall (0 : Rd d) n) (sphere 0 R) D}
    have hF (R : ℝ) : IsClosed (F R) := by
      by_cases hR : (n : ℝ) < R
      · simpa only [F, hR, true_and] using
          (isClosed_le continuous_const
            (DGZ.nd_continuous_setInf (isCompact_closedBall _ _)
              (isCompact_sphere _ _)))
      · have heq : F R = ∅ := by ext D; simp [F, hR]
        rw [heq]
        exact isClosed_empty
    have htail : ∀ θ : ℝ, 0 < θ → ∃ R : ℝ,
        ∀ ν ∈ S, (ν : Measure C(Rd d × Rd d, ℝ)) (F R)ᶜ ≤
          ENNReal.ofReal θ := by
      intro θ hθ
      obtain ⟨R, hR, hpre⟩ :=
        l6a_pure_proper_tail hL1e hDGZ hAdapter P h hh n hθ
      refine ⟨R, ?_⟩
      intro ν hν
      obtain ⟨ε, hε, hνeq⟩ := hν
      rw [hνeq, Measure.map_apply_of_aemeasurable
        (l6a_aemeasurable_raw_metric hDGZ.dim κ hDGZ.kernel ξ hε.1 P h hh)
        (hF R).isOpen_compl.measurableSet]
      change P {ω | ¬ ((n : ℝ) < R ∧
        (n : ℝ) ≤ DGZ.nd_setInf (closedBall (0 : Rd d) n) (sphere 0 R)
          (B ε ω))} ≤ ENNReal.ofReal θ
      simpa only [hR, true_and] using hpre ε hε
    exact l6a_ae_exists_closed_of_uniform_tail S F hF htail μ hμ
  have hall : ∀ᵐ D ∂(μ : Measure C(Rd d × Rd d, ℝ)),
      ∀ n : ℕ, ∃ R : ℝ, (n : ℝ) < R ∧
        (n : ℝ) ≤ DGZ.nd_setInf (closedBall (0 : Rd d) n) (sphere 0 R) D :=
    ae_all_iff.2 hForall
  filter_upwards [hall] with D hD
  exact l6a_proper_of_real_setInf D hD

theorem l6a_pure_closure_good (hL1e : L1e_law)
    {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    (μ : ProbabilityMeasure C(Rd d × Rd d, ℝ))
    (hμ : μ ∈ closure {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
      ∃ ε ∈ Ioo (0 : ℝ) 1,
        (ν : Measure C(Rd d × Rd d, ℝ)) =
          P.map (fun ω => toCMapRd
            ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)))}) :
    ∀ᵐ D ∂(μ : Measure C(Rd d × Rd d, ℝ)),
      IsContinuousMetric D ∧ IsProperFn (d := d) D :=
  (l6a_pure_closure_metric hL1e hDGZ hAdapter P h hh μ hμ).and
    (l6a_pure_closure_proper hL1e hDGZ hAdapter P h hh μ hμ)

end HigherDimLQGMetric
