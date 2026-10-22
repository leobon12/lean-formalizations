import HigherDimLQGMetric.ConvField.Scaling
import HigherDimLQGMetric.ConvField.RadialMain
import HigherDimLQGMetric.LfppTight.MetricScale
import HigherDimLQGMetric.Sphere.Scaling

/-!
# Exact scaling of the LFPP distance

The normalized affine field is formed using its own unit sphere average.  It
agrees almost surely with the paper's `h(r·) - h_r(0)` and has the normalized
LGF law by the existing field invariance theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The normalized affine field has the original normalized LGF law. -/
theorem l6c_map_normalizedAffine_eq {d : ℕ} (hd : 2 ≤ d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {r : ℝ} (hr : 0 < r) :
    P.map (fun ω => addConst (affineComp r 0 (h ω))
      (-sphereAvg (affineComp r 0 (h ω)) 1 0)) = P.map h := by
  calc
    P.map (fun ω => addConst (affineComp r 0 (h ω))
        (-sphereAvg (affineComp r 0 (h ω)) 1 0)) =
      P.map (fun ω => addConst (affineComp r 0 (h ω))
        (-sphereAvg (h ω) r 0)) := by
      apply Measure.map_congr
      filter_upwards [hh.1.ae_sphereAvg_affineComp hd hr 0 one_pos 0]
        with ω hs
      rw [hs]
      simp
    _ = P.map h := hh.map_affineComp_sub_sphereAvg hd hr 0

/-- The exact LFPP scaling identity, on one event independent of the cutoff and
endpoints.  The normalized affine field is `h(r·) - (h(r·))_1(0)`. -/
theorem l6c_ae_lfppDist_scale {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ u v : Rd d,
      lfppDist κ ξ ε (h ω) (r • u, r • v) =
        r * Real.exp (ξ * sphereAvg (h ω) r 0) *
          lfppDist κ ξ (ε / r)
            (addConst (affineComp r 0 (h ω))
              (-sphereAvg (affineComp r 0 (h ω)) 1 0)) (u, v) := by
  let k : Ω → DistRd d := fun ω => affineComp r 0 (h ω)
  have hk : IsWholeSpaceLGF k P := hh.1.affineComp hr 0
  have hconv : ∀ᵐ ω ∂P, k ω ∈ convSet d :=
    hk.ae_exists_tendsto_sphereAvgSeq hd one_pos 0
  let g : Ω → DistRd d := fun ω => addConst (k ω) (-sphereAvg (k ω) 1 0)
  have hg : IsNormalizedLGF g P := hk.isNormalizedLGF_normalize (by omega) hconv
  filter_upwards [l2b_ae_convMollify_scale d hd κ hκ P h hh.1 hr,
    l2b_ae_convMollify_tendsto d hd κ hκ P g hg,
    hh.1.ae_sphereAvg_affineComp hd hr 0 one_pos 0] with ω hscale hlim hsph
  intro ε hε u v
  have heq (z : Rd d) :
      convMollify κ ε (h ω) (r • z) =
        convMollify κ (ε / r) (g ω) z + sphereAvg (h ω) r 0 := by
    have hsh := l2b_convMollify_addConst_of_tendsto hd hκ
      (c := sphereAvg (k ω) 1 0) (div_pos hε hr)
      (hlim (ε / r) (div_pos hε hr) z)
    have hk_eq : addConst (g ω) (sphereAvg (k ω) 1 0) = k ω := by
      dsimp [g]
      rw [addConst_addConst, neg_add_cancel, addConst_zero]
    rw [hk_eq] at hsh
    have hs := hscale ε hε z
    rw [←hs]
    change convMollify κ (ε / r) (k ω) z = _
    rw [hsh]
    congr 1
    simpa only [k, mul_one, smul_zero, zero_add] using hsph
  have h := l6a_lfppDist_scale_of_conv_eq κ ξ ε r (sphereAvg (h ω) r 0)
    hr (h ω) (g ω) 0 u v (by simpa only [zero_add] using heq)
  simpa only [zero_add] using h

end HigherDimLQGMetric
