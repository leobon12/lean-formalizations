import HigherDimLQGMetric.Limits.ScaleIdentity
import HigherDimLQGMetric.LfppTight.MetricScale

/-! Exact LFPP similarity covariance at an arbitrary spatial centre. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_map_normalizedAffine_center_eq {d : ℕ} (hd : 2 ≤ d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {r : ℝ} (hr : 0 < r) (x : Rd d) :
    P.map (fun ω => addConst (affineComp r x (h ω))
      (-sphereAvg (affineComp r x (h ω)) 1 0)) = P.map h := by
  calc
    P.map (fun ω => addConst (affineComp r x (h ω))
        (-sphereAvg (affineComp r x (h ω)) 1 0)) =
      P.map (fun ω => addConst (affineComp r x (h ω))
        (-sphereAvg (h ω) r x)) := by
      apply Measure.map_congr
      filter_upwards [hh.1.ae_sphereAvg_affineComp hd hr x one_pos 0]
        with ω hs
      rw [hs]
      simp
    _ = P.map h := hh.map_affineComp_sub_sphereAvg hd hr x

theorem l6a_ae_lfppDist_scale_center {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {r : ℝ} (hr : 0 < r) (x : Rd d) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ u v : Rd d,
      lfppDist κ ξ ε (h ω) (x + r • u, x + r • v) =
        r * Real.exp (ξ * sphereAvg (h ω) r x) *
          lfppDist κ ξ (ε / r)
            (addConst (affineComp r x (h ω))
              (-sphereAvg (affineComp r x (h ω)) 1 0)) (u, v) := by
  let k : Ω → DistRd d := fun ω => affineComp r x (h ω)
  let t : Ω → DistRd d := fun ω => affineComp 1 x (h ω)
  have ht : IsWholeSpaceLGF t P := hh.1.affineComp one_pos x
  have hk : IsWholeSpaceLGF k P := hh.1.affineComp hr x
  have hconv : ∀ᵐ ω ∂P, k ω ∈ convSet d :=
    hk.ae_exists_tendsto_sphereAvgSeq hd one_pos 0
  let g : Ω → DistRd d := fun ω => addConst (k ω) (-sphereAvg (k ω) 1 0)
  have hg : IsNormalizedLGF g P := hk.isNormalizedLGF_normalize (by omega) hconv
  filter_upwards [l2b_ae_convMollify_scale d hd κ hκ P t ht hr,
    l2b_ae_convMollify_tendsto d hd κ hκ P g hg,
    hh.1.ae_sphereAvg_affineComp hd hr x one_pos 0]
      with ω hscale hlim hsph
  intro ε hε u v
  have hfield (z : Rd d) :
      convMollify κ ε (h ω) (x + r • z) =
        convMollify κ (ε / r) (g ω) z + sphereAvg (h ω) r x := by
    have hsh := l2b_convMollify_addConst_of_tendsto hd hκ
      (c := sphereAvg (k ω) 1 0) (div_pos hε hr)
      (hlim (ε / r) (div_pos hε hr) z)
    have hk_eq : addConst (g ω) (sphereAvg (k ω) 1 0) = k ω := by
      dsimp [g]
      rw [addConst_addConst, neg_add_cancel, addConst_zero]
    rw [hk_eq] at hsh
    have hks : affineComp r 0 (t ω) = k ω := by
      dsimp [t, k]
      rw [affineComp_affineComp]
      simp
    have hs := hscale ε hε z
    rw [hks] at hs
    have htr := l2b_convMollify_comp_translate hd hκ ε (h ω) x (r • z)
    rw [add_comm x (r • z), ←htr, ←hs, hsh]
    congr 1
    simpa only [k, mul_one, smul_zero, zero_add] using hsph
  exact l6a_lfppDist_scale_of_conv_eq κ ξ ε r
    (sphereAvg (h ω) r x) hr (h ω) (g ω) x u v hfield

end HigherDimLQGMetric
