import HigherDimLQGMetric.ConvField.RadialCont

/-! A single almost-sure event for the radial identities of all compact truncations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ} {κ : Rd d → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}

theorem l2b_ae_growth_all (hd : 2 ≤ d) (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ closedBall (0 : Rd d) (N : ℝ), ∀ r : ℝ, 0 < r →
        |sphereAvg (h ω) r z| ≤ C * l2b_growthWeight r := by
  apply ae_all_iff.mpr
  intro N
  have hraw := l2a_sphereAvgGrowth d hd P h hh ((N : ℝ) + 1) (1 / 2)
    (by positivity) (by norm_num)
  filter_upwards [hraw] with ω hω
  obtain ⟨C, hC⟩ := hω
  have hC0 : 0 ≤ C := by
    have hz : (0 : Rd d) ∈ closedBall 0 ((N : ℝ) + 1) := by
      simp [mem_closedBall]
      positivity
    have hc := hC 0 hz 1 one_pos
    norm_num at hc
    linarith [abs_nonneg (sphereAvg (h ω) 1 0)]
  refine ⟨C, hC0, ?_⟩
  intro z hz r hr
  have hz' : z ∈ closedBall (0 : Rd d) ((N : ℝ) + 1) := by
    rw [mem_closedBall, dist_zero_right] at hz ⊢
    linarith
  simpa only [l2b_growthWeight] using hC z hz' r hr

set_option maxHeartbeats 1000000 in
theorem l2b_ae_convTrunc_radial_all (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ), 0 < ε → ∀ z : Rd d, ∀ n : ℕ,
      h ω (convTrunc κ ε z n) =
        ((volume : Measure (Rd d)).toSphere univ).toReal *
          ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
            l2b_axisFactor κ n (Real.log ε) r * sphereAvg (h ω) r z := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (ℝ × Rd d)
  let _ : Countable S := hSc.to_subtype
  have hfix : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ p : S,
      h ω (convTrunc κ (Real.exp p.1.1) p.1.2 n) =
        ((volume : Measure (Rd d)).toSphere univ).toReal *
          ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
            l2b_axisFactor κ n p.1.1 r * sphereAvg (h ω) r p.1.2 := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro p
    filter_upwards [l2b_ae_convTrunc_radial hd hκ hh.1 (Real.exp p.1.1) p.1.2 n]
      with ω hw
    simpa only [l2b_axisFactor] using hw
  filter_upwards [hfix, hh.1.ae_continuousOn_sphereAvg hd,
    l2b_ae_growth_all hd hh] with ω hfix hcont hgrowth
  intro ε hε z n
  let lhs : ℝ × Rd d → ℝ := fun p => h ω (convTrunc κ (Real.exp p.1) p.2 n)
  let rhs : ℝ × Rd d → ℝ := fun p =>
    ((volume : Measure (Rd d)).toSphere univ).toReal *
      ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
        l2b_axisFactor κ n p.1 r * sphereAvg (h ω) r p.2
  have hlhs : Continuous lhs :=
    (h ω).continuous.comp (l2b_continuous_convTrunc_exp hd hκ n)
  have hrhs : Continuous rhs :=
    continuous_const.mul (l2b_continuous_trunc_radial_integral hd hκ n (h ω)
      hcont.2 hgrowth)
  have heq : lhs = rhs := Continuous.ext_on hSd hlhs hrhs (by
    intro p hp
    exact hfix n ⟨p, hp⟩)
  have hp := congrFun heq (Real.log ε, z)
  simpa only [lhs, rhs, Real.exp_log hε] using hp

end HigherDimLQGMetric
