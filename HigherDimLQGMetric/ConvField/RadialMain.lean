import HigherDimLQGMetric.ConvField.RadialLimit

/-! The almost-sure radial formula for the convolution field. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

/-- MA5 Details (c), L2b: the convolution field has the polar formula. -/
def L2b_radial : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d),
    IsNormalizedLGF h P → ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ z : Rd d,
      convMollify κ ε (h ω) z = (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)) *
        ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * sphereAvg (h ω) r z

theorem l2b_sphere_area (d : ℕ) (hd : 2 ≤ d) :
    ((volume : Measure (Rd d)).toSphere univ).toReal =
      2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2) := by
  rw [Measure.toSphere_apply_univ, finrank_euclideanSpace_fin,
    ENNReal.toReal_mul, ENNReal.toReal_natCast]
  exact sphereArea_eq (by omega)

theorem l2b_ae_convMollify_tendsto (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ z : Rd d,
      Tendsto (fun n : ℕ => h ω (convTrunc κ ε z n)) atTop
        (𝓝 (((volume : Measure (Rd d)).toSphere univ).toReal *
          ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
            convKernelEps κ ε (r • e₁ d) * sphereAvg (h ω) r z)) := by
  filter_upwards [l2b_ae_convTrunc_radial_all hd hκ hh,
    hh.1.ae_continuousOn_sphereAvg hd, l2b_ae_growth_all hd hh]
    with ω hrad hcont hgrowth
  intro ε hε z
  have ht := (l2b_tendsto_radial_trunc hd hκ hε (h ω) z hcont.2 hgrowth).const_mul
    ((volume : Measure (Rd d)).toSphere univ).toReal
  convert ht using 1
  funext n
  exact hrad ε hε z n

/-- Exact MA5 statement. -/
theorem l2b_radial : L2b_radial := by
  intro d hd κ hκ Ω _ P _ h hh
  filter_upwards [l2b_ae_convMollify_tendsto d hd κ hκ P h hh] with ω hω
  intro ε hε z
  have hlim := hω ε hε z
  rw [l2b_convMollify_eq_of_tendsto hlim, l2b_sphere_area d hd]

end HigherDimLQGMetric
