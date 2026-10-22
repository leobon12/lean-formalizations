import HigherDimLQGMetric.ConvField.Mass
import HigherDimLQGMetric.ConvField.WholeSpaceLimit

/-! The radial formula also holds for an unnormalized whole-space LGF. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

theorem l2b_ae_radial_wholeSpace (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ z : Rd d,
      convMollify κ ε (h ω) z =
        ((volume : Measure (Rd d)).toSphere univ).toReal *
          ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
            convKernelEps κ ε (r • e₁ d) * sphereAvg (h ω) r z := by
  have hcontH := hh.ae_continuousOn_sphereAvg hd
  have hconv : ∀ᵐ ω ∂P, h ω ∈ convSet d := by
    filter_upwards [hcontH] with ω hω
    exact ⟨_, hω.1 1 one_pos 0⟩
  let g : Ω → DistRd d := fun ω => addConst (h ω) (-sphereAvg (h ω) 1 0)
  have hg : IsNormalizedLGF g P := hh.isNormalizedLGF_normalize (by omega) hconv
  filter_upwards [hcontH, hg.1.ae_continuousOn_sphereAvg hd,
    l2b_ae_growth_all hd hg, l2b_radial d hd κ hκ P g hg,
    l2b_ae_convMollify_tendsto d hd κ hκ P g hg]
    with ω hcontH hcontG hgrowthG hradG hlimG
  intro ε hε z
  let c : ℝ := sphereAvg (h ω) 1 0
  have hEq : ∀ r : ℝ, 0 < r →
      sphereAvg (h ω) r z = sphereAvg (g ω) r z + c := by
    intro r hr
    have hs := sphereAvg_addConst_of_tendsto (by omega : 1 ≤ d)
      (hcontH.1 r hr z) (-c)
    change sphereAvg (g ω) r z = sphereAvg (h ω) r z + -c at hs
    linarith
  let base : ℝ → ℝ := fun r => r ^ (d - 1) * convKernelEps κ ε (r • e₁ d)
  have hgi : IntegrableOn (fun r : ℝ => base r * sphereAvg (g ω) r z) (Ioi (0 : ℝ)) :=
    l2b_integrable_radial_sphereAvg hd hκ hε (g ω) z hcontG.2 hgrowthG
  have hki : IntegrableOn base (Ioi (0 : ℝ)) := l2b_integrable_radial_kernel hd hκ hε
  have hci : IntegrableOn (fun r : ℝ => c * base r) (Ioi (0 : ℝ)) := hki.const_mul c
  have hI : (∫ r in Ioi (0 : ℝ), base r * sphereAvg (h ω) r z) =
      (∫ r in Ioi (0 : ℝ), base r * sphereAvg (g ω) r z) +
        c * (∫ r in Ioi (0 : ℝ), base r) := by
    calc
      _ = ∫ r in Ioi (0 : ℝ), base r * sphereAvg (g ω) r z + c * base r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        change base r * sphereAvg (h ω) r z =
          base r * sphereAvg (g ω) r z + c * base r
        rw [hEq r hr]
        ring
      _ = (∫ r in Ioi (0 : ℝ), base r * sphereAvg (g ω) r z) +
          (∫ r in Ioi (0 : ℝ), c * base r) := integral_add hgi hci
      _ = _ := by rw [integral_const_mul]
  have heq : addConst (g ω) c = h ω := by
    dsimp [g, c]
    simpa only [neg_neg] using (addConst_neg (h ω) (-sphereAvg (h ω) 1 0))
  have hshift : convMollify κ ε (h ω) z = convMollify κ ε (g ω) z + c := by
    rw [← heq]
    exact l2b_convMollify_addConst_of_tendsto hd hκ hε (hlimG ε hε z)
  rw [hshift, hradG ε hε z, ← l2b_sphere_area d hd]
  have hm := l2b_radial_kernel_mass d hd κ hκ hε
  change ((volume : Measure (Rd d)).toSphere univ).toReal *
      (∫ r in Ioi (0 : ℝ), base r * sphereAvg (g ω) r z) + c =
    ((volume : Measure (Rd d)).toSphere univ).toReal *
      (∫ r in Ioi (0 : ℝ), base r * sphereAvg (h ω) r z)
  rw [hI]
  calc
    ((volume : Measure (Rd d)).toSphere univ).toReal *
        (∫ r in Ioi (0 : ℝ), base r * sphereAvg (g ω) r z) + c =
      ((volume : Measure (Rd d)).toSphere univ).toReal *
        (∫ r in Ioi (0 : ℝ), base r * sphereAvg (g ω) r z) +
      c * (((volume : Measure (Rd d)).toSphere univ).toReal *
        ∫ r in Ioi (0 : ℝ), base r) := by rw [show
        ((volume : Measure (Rd d)).toSphere univ).toReal *
          ∫ r in Ioi (0 : ℝ), base r = 1 from hm]; ring
    _ = _ := by ring

end HigherDimLQGMetric
